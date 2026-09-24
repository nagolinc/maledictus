import VcTermSortProofs.Foundation

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 2000000

namespace VcTermSort.Proofs

def continuationIterator {T Tail : Type}
    (outcome : Result (ControlFlow (core.slice.iter.Iter T × Tail) Tail)) :
    Option (core.slice.iter.Iter T) :=
  match outcome with
  | ok (.cont (iter, _)) => some iter
  | _ => none

theorem all_list_element_sorts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Sort)
    (result nextResult : Bool)
    (continued : VcTermSort.all_list_element_sorts_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.all_list_element_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.all_list_element_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeElement, advanced⟩ := pair
      cases maybeElement with
      | none =>
          simp [VcTermSort.all_list_element_sorts_loop.body, observed] at continued
      | some element =>
          have advanced_eq : advanced = next := by
            cases result with
            | false =>
                simp [VcTermSort.all_list_element_sorts_loop.body, observed] at continued
                exact continued.1
            | true =>
                simp [VcTermSort.all_list_element_sorts_loop.body, observed] at continued
                simp only [Bind.bind, Std.bind] at continued
                all_goals repeat' split at continued
                all_goals
                  have mapped := congrArg continuationIterator continued
                  simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced element observed

theorem all_list_element_sorts_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_list_element_sorts_loop.body state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state => VcTermSort.all_list_element_sorts_loop.body state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact all_list_element_sorts_body_decreases state.1 next.1 state.2 next.2 continued

theorem all_list_element_sorts_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_list_element_sorts_loop.body state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.all_list_element_sorts_loop iter result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    all_list_element_sorts_finite_trace iter result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.all_list_element_sorts_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state => VcTermSort.all_list_element_sorts_loop.body state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem all_finite_dict_key_sorts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Sort)
    (result nextResult : Bool)
    (continued : VcTermSort.all_finite_dict_key_sorts_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.all_finite_dict_key_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.all_finite_dict_key_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeElement, advanced⟩ := pair
      cases maybeElement with
      | none =>
          simp [VcTermSort.all_finite_dict_key_sorts_loop.body, observed] at continued
      | some element =>
          have advanced_eq : advanced = next := by
            cases result with
            | false =>
                simp [VcTermSort.all_finite_dict_key_sorts_loop.body, observed] at continued
                exact continued.1
            | true =>
                simp [VcTermSort.all_finite_dict_key_sorts_loop.body, observed] at continued
                simp only [Bind.bind, Std.bind] at continued
                all_goals repeat' split at continued
                all_goals
                  have mapped := congrArg continuationIterator continued
                  simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced element observed

theorem all_finite_dict_key_sorts_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_finite_dict_key_sorts_loop.body state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state => VcTermSort.all_finite_dict_key_sorts_loop.body state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact all_finite_dict_key_sorts_body_decreases state.1 next.1 state.2 next.2 continued

theorem all_finite_dict_key_sorts_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_finite_dict_key_sorts_loop.body state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.all_finite_dict_key_sorts_loop iter result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    all_finite_dict_key_sorts_finite_trace iter result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.all_finite_dict_key_sorts_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state => VcTermSort.all_finite_dict_key_sorts_loop.body state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem all_finite_dict_value_sorts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Sort)
    (result nextResult : Bool)
    (continued : VcTermSort.all_finite_dict_value_sorts_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.all_finite_dict_value_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.all_finite_dict_value_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeElement, advanced⟩ := pair
      cases maybeElement with
      | none =>
          simp [VcTermSort.all_finite_dict_value_sorts_loop.body, observed] at continued
      | some element =>
          have advanced_eq : advanced = next := by
            cases result with
            | false =>
                simp [VcTermSort.all_finite_dict_value_sorts_loop.body, observed] at continued
                exact continued.1
            | true =>
                simp [VcTermSort.all_finite_dict_value_sorts_loop.body, observed] at continued
                simp only [Bind.bind, Std.bind] at continued
                all_goals repeat' split at continued
                all_goals
                  have mapped := congrArg continuationIterator continued
                  simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced element observed

theorem all_finite_dict_value_sorts_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_finite_dict_value_sorts_loop.body state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state => VcTermSort.all_finite_dict_value_sorts_loop.body state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact all_finite_dict_value_sorts_body_decreases state.1 next.1 state.2 next.2 continued

theorem all_finite_dict_value_sorts_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_finite_dict_value_sorts_loop.body state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.all_finite_dict_value_sorts_loop iter result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    all_finite_dict_value_sorts_finite_trace iter result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.all_finite_dict_value_sorts_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state => VcTermSort.all_finite_dict_value_sorts_loop.body state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem require_variadic_tuple_element_sorts_body_decreases
    (expected : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.require_variadic_tuple_element_sorts_loop.body
      expected iter result = .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeValue, advanced⟩ := pair
      cases maybeValue with
      | none =>
          simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body, observed] at continued
      | some value =>
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body, observed,
                      isOkObserved] at continued
                    exact continued.1
                | true =>
                    simp [VcTermSort.require_variadic_tuple_element_sorts_loop.body, observed,
                      isOkObserved] at continued
                    simp only [Bind.bind, Std.bind] at continued
                    all_goals repeat' split at continued
                    all_goals
                      have mapped := congrArg continuationIterator continued
                      simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced value observed

theorem require_variadic_tuple_element_sorts_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.Term) (expected : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.require_variadic_tuple_element_sorts_loop.body
          expected state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state => VcTermSort.require_variadic_tuple_element_sorts_loop.body
      expected state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact require_variadic_tuple_element_sorts_body_decreases
    expected state.1 next.1 state.2 next.2 continued

theorem require_variadic_tuple_element_sorts_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.Term) (expected : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.require_variadic_tuple_element_sorts_loop.body
          expected state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.require_variadic_tuple_element_sorts_loop
        iter expected result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    require_variadic_tuple_element_sorts_finite_trace iter expected result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.require_variadic_tuple_element_sorts_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state => VcTermSort.require_variadic_tuple_element_sorts_loop.body
      expected state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem all_nominal_references_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : Bool)
    (continued : VcTermSort.all_nominal_references_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.all_nominal_references_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.all_nominal_references_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeValue, advanced⟩ := pair
      cases maybeValue with
      | none =>
          simp [VcTermSort.all_nominal_references_loop.body, observed] at continued
      | some value =>
          have advanced_eq : advanced = next := by
            cases result <;> cases value <;>
              simp [VcTermSort.all_nominal_references_loop.body, observed] at continued <;>
              simp_all
          subst next
          exact slice_iterator_next_some_decreases iter advanced value observed

theorem all_nominal_references_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.Term) (result : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.all_nominal_references_loop.body state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state => VcTermSort.all_nominal_references_loop.body state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact all_nominal_references_body_decreases state.1 next.1 state.2 next.2 continued

theorem all_nominal_references_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.Term) (result : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.all_nominal_references_loop.body state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.all_nominal_references_loop iter result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    all_nominal_references_finite_trace iter result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.all_nominal_references_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state => VcTermSort.all_nominal_references_loop.body state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem all_nominal_reference_keys_body_decreases
    (iter next : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result nextResult : Bool)
    (continued : VcTermSort.all_nominal_reference_keys_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.all_nominal_reference_keys_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.all_nominal_reference_keys_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeEntry, advanced⟩ := pair
      cases maybeEntry with
      | none =>
          simp [VcTermSort.all_nominal_reference_keys_loop.body, observed] at continued
      | some entry =>
          obtain ⟨key, value⟩ := entry
          have advanced_eq : advanced = next := by
            cases result <;> cases key <;>
              simp [VcTermSort.all_nominal_reference_keys_loop.body, observed] at continued <;>
              simp_all
          subst next
          exact slice_iterator_next_some_decreases iter advanced (key, value) observed

theorem all_nominal_reference_keys_finite_trace
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.all_nominal_reference_keys_loop.body state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state => VcTermSort.all_nominal_reference_keys_loop.body state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact all_nominal_reference_keys_body_decreases
    state.1 next.1 state.2 next.2 continued

theorem all_nominal_reference_keys_loop_bound
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.all_nominal_reference_keys_loop.body state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.all_nominal_reference_keys_loop iter result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    all_nominal_reference_keys_finite_trace iter result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.all_nominal_reference_keys_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state => VcTermSort.all_nominal_reference_keys_loop.body state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem validate_int_enum_descriptor_body_decreases
    (iter next : core.slice.iter.Iter (String × Std.I64))
    (names nextNames : alloc.collections.btree.set.BTreeSet String Global)
    (values nextValues : alloc.collections.btree.set.BTreeSet Std.I64 Global)
    (valid nextValid : Bool)
    (continued : VcTermSort.validate_int_enum_descriptor_loop.body
      iter names values valid =
      .ok (.cont (next, nextNames, nextValues, nextValid))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.validate_int_enum_descriptor_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.validate_int_enum_descriptor_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeEntry, advanced⟩ := pair
      cases maybeEntry with
      | none =>
          simp [VcTermSort.validate_int_enum_descriptor_loop.body, observed] at continued
      | some entry =>
          obtain ⟨memberName, value⟩ := entry
          have advanced_eq : advanced = next := by
            cases valid with
            | false =>
                simp_all [VcTermSort.validate_int_enum_descriptor_loop.body]
            | true =>
                simp [VcTermSort.validate_int_enum_descriptor_loop.body, observed] at continued
                cases emptyObserved : alloc.string.String.is_empty memberName with
                | fail error => simp [emptyObserved] at continued
                | div => simp [emptyObserved] at continued
                | ok isEmpty =>
                    cases isEmpty with
                    | true => simp_all
                    | false =>
                        cases cloneObserved :
                            alloc.string.String.Insts.CoreCloneClone.clone memberName with
                        | fail error => simp [emptyObserved, cloneObserved] at continued
                        | div => simp [emptyObserved, cloneObserved] at continued
                        | ok clonedName =>
                            cases namesObserved :
                                alloc.collections.btree.set.BTreeSet.insert
                                  core.core.clone.CloneGlobal
                                  alloc.string.String.Insts.CoreCmpOrd names clonedName with
                            | fail error =>
                                simp [emptyObserved, cloneObserved, namesObserved] at continued
                            | div =>
                                simp [emptyObserved, cloneObserved, namesObserved] at continued
                            | ok namesResult =>
                                obtain ⟨nameFresh, updatedNames⟩ := namesResult
                                cases nameFresh with
                                | false =>
                                    simp_all
                                | true =>
                                    cases valuesObserved :
                                        alloc.collections.btree.set.BTreeSet.insert
                                          core.core.clone.CloneGlobal core.cmp.OrdI64
                                          values value with
                                    | fail error =>
                                        simp [emptyObserved, cloneObserved, namesObserved,
                                          valuesObserved] at continued
                                    | div =>
                                        simp [emptyObserved, cloneObserved, namesObserved,
                                          valuesObserved] at continued
                                    | ok valuesResult =>
                                        obtain ⟨valueFresh, updatedValues⟩ := valuesResult
                                        simp_all
          subst next
          exact slice_iterator_next_some_decreases iter advanced (memberName, value) observed

theorem validate_int_enum_descriptor_finite_trace
    (iter : core.slice.iter.Iter (String × Std.I64))
    (names : alloc.collections.btree.set.BTreeSet String Global)
    (values : alloc.collections.btree.set.BTreeSet Std.I64 Global)
    (valid : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.validate_int_enum_descriptor_loop.body
            state.1 state.2.1 state.2.2.1 state.2.2.2)
        steps (iter, names, values, valid) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state =>
      VcTermSort.validate_int_enum_descriptor_loop.body
        state.1 state.2.1 state.2.2.1 state.2.2.2)
    (fun state => sliceIteratorRemaining state.1) ?_
    (iter, names, values, valid)
  intro state next continued
  exact validate_int_enum_descriptor_body_decreases
    state.1 next.1
    state.2.1 next.2.1
    state.2.2.1 next.2.2.1
    state.2.2.2 next.2.2.2
    continued

theorem validate_int_enum_descriptor_loop_bound
    (iter : core.slice.iter.Iter (String × Std.I64))
    (names : alloc.collections.btree.set.BTreeSet String Global)
    (values : alloc.collections.btree.set.BTreeSet Std.I64 Global)
    (valid : Bool) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.validate_int_enum_descriptor_loop.body
            state.1 state.2.1 state.2.2.1 state.2.2.2)
        steps (iter, names, values, valid) output ∧
      VcTermSort.validate_int_enum_descriptor_loop iter names values valid = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    validate_int_enum_descriptor_finite_trace iter names values valid
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.validate_int_enum_descriptor_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state =>
      VcTermSort.validate_int_enum_descriptor_loop.body
        state.1 state.2.1 state.2.2.1 state.2.2.2)
    (iter, names, values, valid) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem require_predicate_argument_sorts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.require_predicate_argument_sorts_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.require_predicate_argument_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.require_predicate_argument_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeArgument, advanced⟩ := pair
      cases maybeArgument with
      | none =>
          simp [VcTermSort.require_predicate_argument_sorts_loop.body, observed] at continued
      | some argument =>
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSort.require_predicate_argument_sorts_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSort.require_predicate_argument_sorts_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
              cases isOk with
              | false =>
                  simp [VcTermSort.require_predicate_argument_sorts_loop.body, observed,
                    isOkObserved] at continued
                  simp_all
              | true =>
                cases sortObserved : VcTermSort.Term.sort_typed argument with
                | fail error =>
                    simp [VcTermSort.require_predicate_argument_sorts_loop.body, observed,
                      isOkObserved, sortObserved] at continued
                | div =>
                    simp [VcTermSort.require_predicate_argument_sorts_loop.body, observed,
                      isOkObserved, sortObserved] at continued
                | ok sorted =>
                    cases sorted with
                    | Err error =>
                        simp [VcTermSort.require_predicate_argument_sorts_loop.body, observed,
                          isOkObserved, sortObserved] at continued
                        simp_all
                    | Ok sort =>
                        cases sort <;>
                          simp [VcTermSort.require_predicate_argument_sorts_loop.body, observed,
                            isOkObserved, sortObserved] at continued
                        all_goals
                          first
                          | simp_all
                          | cases ownedObserved :
                              Str.Insts.AllocBorrowToOwnedString.to_owned
                                (toStr
                                  "predicate instance arguments must have a first-order scalar, reference, or class sort") <;>
                              simp_all
          subst next
          exact slice_iterator_next_some_decreases iter advanced argument observed

theorem require_predicate_argument_sorts_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.require_predicate_argument_sorts_loop.body state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state =>
      VcTermSort.require_predicate_argument_sorts_loop.body state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact require_predicate_argument_sorts_body_decreases
    state.1 next.1 state.2 next.2 continued

theorem require_predicate_argument_sorts_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.require_predicate_argument_sorts_loop.body state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.require_predicate_argument_sorts_loop iter result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    require_predicate_argument_sorts_finite_trace iter result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.require_predicate_argument_sorts_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state =>
      VcTermSort.require_predicate_argument_sorts_loop.body state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem require_permission_transfer_amounts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.require_permission_transfer_amounts_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSort.require_permission_transfer_amounts_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.require_permission_transfer_amounts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeAmount, advanced⟩ := pair
      cases maybeAmount with
      | none =>
          simp [VcTermSort.require_permission_transfer_amounts_loop.body, observed] at continued
      | some amount =>
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSort.require_permission_transfer_amounts_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSort.require_permission_transfer_amounts_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
              cases isOk with
              | false =>
                  simp [VcTermSort.require_permission_transfer_amounts_loop.body, observed,
                    isOkObserved] at continued
                  simp_all
              | true =>
                  cases requiredObserved : VcTermSort.require_sort amount.receiver
                    VcTermSort.Sort.Reference
                      VcTermSort.SortContext.PermissionTransferReceiver with
                  | fail error =>
                      simp [VcTermSort.require_permission_transfer_amounts_loop.body, observed,
                        isOkObserved, requiredObserved] at continued
                  | div =>
                      simp [VcTermSort.require_permission_transfer_amounts_loop.body, observed,
                        isOkObserved, requiredObserved] at continued
                  | ok required =>
                      cases required with
                      | Err error =>
                          simp [VcTermSort.require_permission_transfer_amounts_loop.body,
                            observed, isOkObserved, requiredObserved] at continued
                          simp_all
                      | Ok unitValue =>
                          by_cases denominatorZero : amount.denominator = 0#u32
                          · simp [VcTermSort.require_permission_transfer_amounts_loop.body,
                              observed, isOkObserved, requiredObserved, denominatorZero] at continued
                            exact continued.1
                          · by_cases numeratorTooLarge :
                              (amount.denominator.val : Nat) < amount.numerator.val
                            · simp [VcTermSort.require_permission_transfer_amounts_loop.body,
                                observed, isOkObserved, requiredObserved, denominatorZero] at continued
                              simp [numeratorTooLarge] at continued
                              exact continued.1
                            · simp [VcTermSort.require_permission_transfer_amounts_loop.body,
                                observed, isOkObserved, requiredObserved, denominatorZero] at continued
                              simp [numeratorTooLarge] at continued
                              exact continued.1
          subst next
          exact slice_iterator_next_some_decreases iter advanced amount observed

theorem require_permission_transfer_amounts_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.require_permission_transfer_amounts_loop.body state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state =>
      VcTermSort.require_permission_transfer_amounts_loop.body state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact require_permission_transfer_amounts_body_decreases
    state.1 next.1 state.2 next.2 continued

theorem require_permission_transfer_amounts_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.require_permission_transfer_amounts_loop.body state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.require_permission_transfer_amounts_loop iter result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    require_permission_transfer_amounts_finite_trace iter result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.require_permission_transfer_amounts_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state =>
      VcTermSort.require_permission_transfer_amounts_loop.body state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem two_bind_cont_iterator_first {A B T : Type}
    (first : Result A) (second : A → Result B)
    (advanced next : core.slice.iter.Iter T) (nextValue : B)
    (continued :
      (do
        let firstValue ← first
        let secondValue ← second firstValue
        ok (cont (advanced, secondValue) :
          ControlFlow (core.slice.iter.Iter T × B) B)) =
      ok (cont (next, nextValue) : ControlFlow (core.slice.iter.Iter T × B) B)) :
    advanced = next := by
  cases first with
  | fail error => simp [Bind.bind, Std.bind] at continued
  | div => simp [Bind.bind, Std.bind] at continued
  | ok firstValue =>
      cases secondObserved : second firstValue with
      | fail error => simp [Bind.bind, Std.bind, secondObserved] at continued
      | div => simp [Bind.bind, Std.bind, secondObserved] at continued
      | ok secondValue =>
          simp [Bind.bind, Std.bind, secondObserved] at continued
          exact continued.1

theorem one_bind_cont_iterator_first {A Tail T : Type}
    (first : Result A) (tail : A → Tail)
    (advanced next : core.slice.iter.Iter T) (nextTail : Tail)
    (continued :
      (do
        let value ← first
        ok (cont (advanced, tail value) :
          ControlFlow (core.slice.iter.Iter T × Tail) Tail)) =
      ok (cont (next, nextTail) : ControlFlow (core.slice.iter.Iter T × Tail) Tail)) :
    advanced = next := by
  cases firstObserved : first with
  | fail error => simp [Bind.bind, Std.bind, firstObserved] at continued
  | div => simp [Bind.bind, Std.bind, firstObserved] at continued
  | ok value =>
      simp [Bind.bind, Std.bind, firstObserved] at continued
      exact continued.1

theorem require_all_sorts_body_decreases
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.require_all_sorts_loop.body expected context iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
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
          have advanced_eq : advanced = next := by
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
          exact slice_iterator_next_some_decreases iter advanced value observed

theorem require_all_sorts_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.require_all_sorts_loop.body expected context state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state =>
      VcTermSort.require_all_sorts_loop.body expected context state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact require_all_sorts_body_decreases expected context
    state.1 next.1 state.2 next.2 continued

theorem require_all_sorts_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.require_all_sorts_loop.body expected context state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.require_all_sorts_loop iter expected context result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    require_all_sorts_finite_trace iter expected context result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.require_all_sorts_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state =>
      VcTermSort.require_all_sorts_loop.body expected context state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem collect_sorts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (sorts nextSorts : VcTermSort.ModelVec VcTermSort.Sort)
    (error nextError : Option VcTermSort.SortError)
    (continued : VcTermSort.collect_sorts_loop.body iter sorts error =
      .ok (.cont (next, nextSorts, nextError))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
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
          have advanced_eq : advanced = next := by
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
                | ok sorted =>
                    cases sorted with
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
          exact slice_iterator_next_some_decreases iter advanced value observed

theorem collect_sorts_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (sorts : VcTermSort.ModelVec VcTermSort.Sort) (error : Option VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.collect_sorts_loop.body state.1 state.2.1 state.2.2)
        steps (iter, sorts, error) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state =>
      VcTermSort.collect_sorts_loop.body state.1 state.2.1 state.2.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, sorts, error)
  intro state next continued
  exact collect_sorts_body_decreases
    state.1 next.1 state.2.1 next.2.1 state.2.2 next.2.2 continued

theorem collect_sorts_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (sorts : VcTermSort.ModelVec VcTermSort.Sort) (error : Option VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.collect_sorts_loop.body state.1 state.2.1 state.2.2)
        steps (iter, sorts, error) output ∧
      VcTermSort.collect_sorts_loop iter sorts error = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    collect_sorts_finite_trace iter sorts error
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.collect_sorts_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state =>
      VcTermSort.collect_sorts_loop.body state.1 state.2.1 state.2.2)
    (iter, sorts, error) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem require_finite_dict_entry_sorts_body_decreases
    (keySort valueSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.require_finite_dict_entry_sorts_loop.body
      keySort valueSort iter result = .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSort.require_finite_dict_entry_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.require_finite_dict_entry_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeEntry, advanced⟩ := pair
      cases maybeEntry with
      | none =>
          simp [VcTermSort.require_finite_dict_entry_sorts_loop.body, observed] at continued
      | some entry =>
          obtain ⟨key, value⟩ := entry
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSort.require_finite_dict_entry_sorts_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSort.require_finite_dict_entry_sorts_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
              cases isOk with
              | false =>
                  simp [VcTermSort.require_finite_dict_entry_sorts_loop.body, observed,
                    isOkObserved] at continued
                  exact continued.1
              | true =>
                  simp [VcTermSort.require_finite_dict_entry_sorts_loop.body, observed,
                    isOkObserved] at continued
                  simp only [Bind.bind, Std.bind] at continued
                  all_goals repeat' split at continued
                  all_goals
                    have mapped := congrArg continuationIterator continued
                    simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced (key, value) observed

theorem require_finite_dict_entry_sorts_finite_trace
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (keySort valueSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.require_finite_dict_entry_sorts_loop.body
            keySort valueSort state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state =>
      VcTermSort.require_finite_dict_entry_sorts_loop.body
        keySort valueSort state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact require_finite_dict_entry_sorts_body_decreases keySort valueSort
    state.1 next.1 state.2 next.2 continued

theorem require_finite_dict_entry_sorts_loop_bound
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (keySort valueSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.require_finite_dict_entry_sorts_loop.body
            keySort valueSort state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.require_finite_dict_entry_sorts_loop
        iter keySort valueSort result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    require_finite_dict_entry_sorts_finite_trace iter keySort valueSort result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.require_finite_dict_entry_sorts_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state =>
      VcTermSort.require_finite_dict_entry_sorts_loop.body
        keySort valueSort state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem validate_bound_occurrences_all_body_decreases
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.validate_bound_occurrences.all_loop.body
      binder binderSort iter result = .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSort.validate_bound_occurrences.all_loop.body, observed] at continued
  | div =>
      simp [VcTermSort.validate_bound_occurrences.all_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeTerm, advanced⟩ := pair
      cases maybeTerm with
      | none =>
          simp [VcTermSort.validate_bound_occurrences.all_loop.body, observed] at continued
      | some term =>
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail isOkError =>
                simp [VcTermSort.validate_bound_occurrences.all_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSort.validate_bound_occurrences.all_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSort.validate_bound_occurrences.all_loop.body, observed,
                      isOkObserved] at continued
                    exact continued.1
                | true =>
                    simp [VcTermSort.validate_bound_occurrences.all_loop.body, observed,
                      isOkObserved] at continued
                    exact one_bind_cont_iterator_first
                      (VcTermSort.validate_bound_occurrences.one term binder binderSort)
                      (fun checked => checked)
                      advanced next nextResult continued
          subst next
          exact slice_iterator_next_some_decreases iter advanced term observed

theorem validate_bound_occurrences_all_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.validate_bound_occurrences.all_loop.body
            binder binderSort state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state =>
      VcTermSort.validate_bound_occurrences.all_loop.body
        binder binderSort state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact validate_bound_occurrences_all_body_decreases
    binder binderSort state.1 next.1 state.2 next.2 continued

theorem validate_bound_occurrences_all_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.Term)
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.validate_bound_occurrences.all_loop.body
            binder binderSort state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.validate_bound_occurrences.all_loop
        iter binder binderSort result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    validate_bound_occurrences_all_finite_trace iter binder binderSort result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.validate_bound_occurrences.all_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state =>
      VcTermSort.validate_bound_occurrences.all_loop.body
        binder binderSort state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem validate_bound_occurrences_all_transfers_body_decreases
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.validate_bound_occurrences.all_transfers_loop.body
      binder binderSort iter result = .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
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
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail isOkError =>
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
                      (fun checked => checked)
                      advanced next nextResult continued
          subst next
          exact slice_iterator_next_some_decreases iter advanced amount observed

theorem validate_bound_occurrences_all_transfers_finite_trace
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.validate_bound_occurrences.all_transfers_loop.body
            binder binderSort state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state =>
      VcTermSort.validate_bound_occurrences.all_transfers_loop.body
        binder binderSort state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact validate_bound_occurrences_all_transfers_body_decreases
    binder binderSort state.1 next.1 state.2 next.2 continued

theorem validate_bound_occurrences_all_transfers_loop_bound
    (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.validate_bound_occurrences.all_transfers_loop.body
            binder binderSort state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.validate_bound_occurrences.all_transfers_loop
        iter binder binderSort result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    validate_bound_occurrences_all_transfers_finite_trace
      iter binder binderSort result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.validate_bound_occurrences.all_transfers_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state =>
      VcTermSort.validate_bound_occurrences.all_transfers_loop.body
        binder binderSort state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

theorem validate_bound_occurrences_all_entries_body_decreases
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSort.validate_bound_occurrences.all_entries_loop.body
      binder binderSort iter result = .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
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
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail isOkError =>
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
                      (fun checked => checked)
                      advanced next nextResult continued
          subst next
          exact slice_iterator_next_some_decreases iter advanced (key, value) observed

theorem validate_bound_occurrences_all_entries_finite_trace
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.validate_bound_occurrences.all_entries_loop.body
            binder binderSort state.1 state.2)
        steps (iter, result) output := by
  refine finite_loop_trace_exists_of_decreases
    (fun state =>
      VcTermSort.validate_bound_occurrences.all_entries_loop.body
        binder binderSort state.1 state.2)
    (fun state => sliceIteratorRemaining state.1) ?_ (iter, result)
  intro state next continued
  exact validate_bound_occurrences_all_entries_body_decreases
    binder binderSort state.1 next.1 state.2 next.2 continued

theorem validate_bound_occurrences_all_entries_loop_bound
    (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (binder : String) (binderSort : VcTermSort.Sort)
    (result : core.result.Result Unit VcTermSort.SortError) :
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state =>
          VcTermSort.validate_bound_occurrences.all_entries_loop.body
            binder binderSort state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.validate_bound_occurrences.all_entries_loop
        iter binder binderSort result = output := by
  obtain ⟨steps, output, bounded, trace⟩ :=
    validate_bound_occurrences_all_entries_finite_trace
      iter binder binderSort result
  obtain ⟨headroom, fuel_eq⟩ := Nat.exists_eq_add_of_le bounded
  refine ⟨steps, output, bounded, trace, ?_⟩
  unfold VcTermSort.validate_bound_occurrences.all_entries_loop
  change VcTermSort.runLoopFuel (sliceIteratorRemaining iter + 1)
    (fun state =>
      VcTermSort.validate_bound_occurrences.all_entries_loop.body
        binder binderSort state.1 state.2)
    (iter, result) = output
  rw [fuel_eq]
  exact run_loop_fuel_with_headroom_of_trace trace headroom

end VcTermSort.Proofs
