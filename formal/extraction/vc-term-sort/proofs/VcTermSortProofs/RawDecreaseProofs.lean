import VcTermSortProofs.Foundation
import VcTermSort.Code.RawFuns

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 2000000

namespace VcTermSort.RawProofs

open VcTermSort.Proofs

def continuationIterator {T Tail : Type}
    (outcome : Result (ControlFlow (core.slice.iter.Iter T × Tail) Tail)) :
    Option (core.slice.iter.Iter T) :=
  match outcome with
  | ok (.cont (iter, _)) => some iter
  | _ => none

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

theorem all_list_element_sorts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Sort)
    (result nextResult : Bool)
    (continued : VcTermSortRaw.all_list_element_sorts_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSortRaw.all_list_element_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.all_list_element_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeElement, advanced⟩ := pair
      cases maybeElement with
      | none =>
          simp [VcTermSortRaw.all_list_element_sorts_loop.body, observed] at continued
      | some element =>
          have advanced_eq : advanced = next := by
            cases result with
            | false =>
                simp [VcTermSortRaw.all_list_element_sorts_loop.body, observed] at continued
                exact continued.1
            | true =>
                simp [VcTermSortRaw.all_list_element_sorts_loop.body, observed] at continued
                simp only [Bind.bind, Std.bind] at continued
                all_goals repeat' split at continued
                all_goals
                  have mapped := congrArg continuationIterator continued
                  simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced element observed

theorem all_finite_dict_key_sorts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Sort)
    (result nextResult : Bool)
    (continued : VcTermSortRaw.all_finite_dict_key_sorts_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSortRaw.all_finite_dict_key_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.all_finite_dict_key_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeElement, advanced⟩ := pair
      cases maybeElement with
      | none =>
          simp [VcTermSortRaw.all_finite_dict_key_sorts_loop.body, observed] at continued
      | some element =>
          have advanced_eq : advanced = next := by
            cases result with
            | false =>
                simp [VcTermSortRaw.all_finite_dict_key_sorts_loop.body, observed] at continued
                exact continued.1
            | true =>
                simp [VcTermSortRaw.all_finite_dict_key_sorts_loop.body, observed] at continued
                simp only [Bind.bind, Std.bind] at continued
                all_goals repeat' split at continued
                all_goals
                  have mapped := congrArg continuationIterator continued
                  simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced element observed

theorem all_finite_dict_value_sorts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Sort)
    (result nextResult : Bool)
    (continued : VcTermSortRaw.all_finite_dict_value_sorts_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSortRaw.all_finite_dict_value_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.all_finite_dict_value_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeElement, advanced⟩ := pair
      cases maybeElement with
      | none =>
          simp [VcTermSortRaw.all_finite_dict_value_sorts_loop.body, observed] at continued
      | some element =>
          have advanced_eq : advanced = next := by
            cases result with
            | false =>
                simp [VcTermSortRaw.all_finite_dict_value_sorts_loop.body, observed] at continued
                exact continued.1
            | true =>
                simp [VcTermSortRaw.all_finite_dict_value_sorts_loop.body, observed] at continued
                simp only [Bind.bind, Std.bind] at continued
                all_goals repeat' split at continued
                all_goals
                  have mapped := congrArg continuationIterator continued
                  simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced element observed

theorem require_variadic_tuple_element_sorts_body_decreases
    (expected : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSortRaw.require_variadic_tuple_element_sorts_loop.body
      expected iter result = .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSortRaw.require_variadic_tuple_element_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.require_variadic_tuple_element_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeValue, advanced⟩ := pair
      cases maybeValue with
      | none =>
          simp [VcTermSortRaw.require_variadic_tuple_element_sorts_loop.body, observed] at continued
      | some value =>
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSortRaw.require_variadic_tuple_element_sorts_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSortRaw.require_variadic_tuple_element_sorts_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSortRaw.require_variadic_tuple_element_sorts_loop.body, observed,
                      isOkObserved] at continued
                    exact continued.1
                | true =>
                    simp [VcTermSortRaw.require_variadic_tuple_element_sorts_loop.body, observed,
                      isOkObserved] at continued
                    simp only [Bind.bind, Std.bind] at continued
                    all_goals repeat' split at continued
                    all_goals
                      have mapped := congrArg continuationIterator continued
                      simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced value observed

theorem all_nominal_references_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : Bool)
    (continued : VcTermSortRaw.all_nominal_references_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSortRaw.all_nominal_references_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.all_nominal_references_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeValue, advanced⟩ := pair
      cases maybeValue with
      | none =>
          simp [VcTermSortRaw.all_nominal_references_loop.body, observed] at continued
      | some value =>
          have advanced_eq : advanced = next := by
            cases result <;> cases value <;>
              simp [VcTermSortRaw.all_nominal_references_loop.body, observed] at continued <;>
              simp_all
          subst next
          exact slice_iterator_next_some_decreases iter advanced value observed

theorem all_nominal_reference_keys_body_decreases
    (iter next : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result nextResult : Bool)
    (continued : VcTermSortRaw.all_nominal_reference_keys_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSortRaw.all_nominal_reference_keys_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.all_nominal_reference_keys_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeEntry, advanced⟩ := pair
      cases maybeEntry with
      | none =>
          simp [VcTermSortRaw.all_nominal_reference_keys_loop.body, observed] at continued
      | some entry =>
          obtain ⟨key, value⟩ := entry
          have advanced_eq : advanced = next := by
            cases result <;> cases key <;>
              simp [VcTermSortRaw.all_nominal_reference_keys_loop.body, observed] at continued <;>
              simp_all
          subst next
          exact slice_iterator_next_some_decreases iter advanced (key, value) observed

theorem validate_int_enum_descriptor_body_decreases
    (iter next : core.slice.iter.Iter (String × Std.I64))
    (names nextNames : alloc.collections.btree.set.BTreeSet String Global)
    (values nextValues : alloc.collections.btree.set.BTreeSet Std.I64 Global)
    (valid nextValid : Bool)
    (continued : VcTermSortRaw.validate_int_enum_descriptor_loop.body
      iter names values valid =
      .ok (.cont (next, nextNames, nextValues, nextValid))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSortRaw.validate_int_enum_descriptor_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.validate_int_enum_descriptor_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeEntry, advanced⟩ := pair
      cases maybeEntry with
      | none =>
          simp [VcTermSortRaw.validate_int_enum_descriptor_loop.body, observed] at continued
      | some entry =>
          obtain ⟨memberName, value⟩ := entry
          have advanced_eq : advanced = next := by
            cases valid with
            | false =>
                simp_all [VcTermSortRaw.validate_int_enum_descriptor_loop.body]
            | true =>
                simp [VcTermSortRaw.validate_int_enum_descriptor_loop.body, observed] at continued
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

theorem require_predicate_argument_sorts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSortRaw.require_predicate_argument_sorts_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSortRaw.require_predicate_argument_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.require_predicate_argument_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeArgument, advanced⟩ := pair
      cases maybeArgument with
      | none =>
          simp [VcTermSortRaw.require_predicate_argument_sorts_loop.body, observed] at continued
      | some argument =>
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSortRaw.require_predicate_argument_sorts_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSortRaw.require_predicate_argument_sorts_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
              cases isOk with
              | false =>
                  simp [VcTermSortRaw.require_predicate_argument_sorts_loop.body, observed,
                    isOkObserved] at continued
                  simp_all
              | true =>
                cases sortObserved : VcTermSortRaw.Term.sort_typed argument with
                | fail error =>
                    simp [VcTermSortRaw.require_predicate_argument_sorts_loop.body, observed,
                      isOkObserved, sortObserved] at continued
                | div =>
                    simp [VcTermSortRaw.require_predicate_argument_sorts_loop.body, observed,
                      isOkObserved, sortObserved] at continued
                | ok sorted =>
                    cases sorted with
                    | Err error =>
                        simp [VcTermSortRaw.require_predicate_argument_sorts_loop.body, observed,
                          isOkObserved, sortObserved] at continued
                        simp_all
                    | Ok sort =>
                        cases sort <;>
                          simp [VcTermSortRaw.require_predicate_argument_sorts_loop.body, observed,
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

theorem require_permission_transfer_amounts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSortRaw.require_permission_transfer_amounts_loop.body iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeAmount, advanced⟩ := pair
      cases maybeAmount with
      | none =>
          simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body, observed] at continued
      | some amount =>
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
              cases isOk with
              | false =>
                  simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body, observed,
                    isOkObserved] at continued
                  simp_all
              | true =>
                  cases requiredObserved : VcTermSortRaw.require_sort amount.receiver
                    VcTermSort.Sort.Reference
                      VcTermSort.SortContext.PermissionTransferReceiver with
                  | fail error =>
                      simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body, observed,
                        isOkObserved, requiredObserved] at continued
                  | div =>
                      simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body, observed,
                        isOkObserved, requiredObserved] at continued
                  | ok required =>
                      cases required with
                      | Err error =>
                          simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body,
                            observed, isOkObserved, requiredObserved] at continued
                          simp_all
                      | Ok unitValue =>
                          by_cases denominatorZero : amount.denominator = 0#u32
                          · simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body,
                              observed, isOkObserved, requiredObserved, denominatorZero] at continued
                            exact continued.1
                          · by_cases numeratorTooLarge :
                              (amount.denominator.val : Nat) < amount.numerator.val
                            · simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body,
                                observed, isOkObserved, requiredObserved, denominatorZero] at continued
                              simp [numeratorTooLarge] at continued
                              exact continued.1
                            · simp [VcTermSortRaw.require_permission_transfer_amounts_loop.body,
                                observed, isOkObserved, requiredObserved, denominatorZero] at continued
                              simp [numeratorTooLarge] at continued
                              exact continued.1
          subst next
          exact slice_iterator_next_some_decreases iter advanced amount observed

theorem require_all_sorts_body_decreases
    (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSortRaw.require_all_sorts_loop.body expected context iter result =
      .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail error =>
      simp [VcTermSortRaw.require_all_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.require_all_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeValue, advanced⟩ := pair
      cases maybeValue with
      | none =>
          simp [VcTermSortRaw.require_all_sorts_loop.body, observed] at continued
      | some value =>
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSortRaw.require_all_sorts_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSortRaw.require_all_sorts_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
              cases isOk with
              | false =>
                  simp [VcTermSortRaw.require_all_sorts_loop.body, observed,
                    isOkObserved] at continued
                  simp_all
              | true =>
                  simp [VcTermSortRaw.require_all_sorts_loop.body, observed,
                    isOkObserved] at continued
                  exact two_bind_cont_iterator_first
                    (VcTermSort.Sort.Insts.CoreCloneClone.clone expected)
                    (fun cloned => VcTermSortRaw.require_sort value cloned context)
                    advanced next nextResult continued
          subst next
          exact slice_iterator_next_some_decreases iter advanced value observed

theorem collect_sorts_body_decreases
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (sorts nextSorts : VcTermSort.ModelVec VcTermSort.Sort)
    (error nextError : Option VcTermSort.SortError)
    (continued : VcTermSortRaw.collect_sorts_loop.body iter sorts error =
      .ok (.cont (next, nextSorts, nextError))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSortRaw.collect_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.collect_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeValue, advanced⟩ := pair
      cases maybeValue with
      | none =>
          simp [VcTermSortRaw.collect_sorts_loop.body, observed] at continued
      | some value =>
          have advanced_eq : advanced = next := by
            cases error with
            | some current =>
                simp [VcTermSortRaw.collect_sorts_loop.body, observed] at continued
                exact continued.1
            | none =>
                cases sortObserved : VcTermSortRaw.Term.sort_typed value with
                | fail sortError =>
                    simp [VcTermSortRaw.collect_sorts_loop.body, observed,
                      sortObserved] at continued
                | div =>
                    simp [VcTermSortRaw.collect_sorts_loop.body, observed,
                      sortObserved] at continued
                | ok sorted =>
                    cases sorted with
                    | Err current =>
                        simp [VcTermSortRaw.collect_sorts_loop.body, observed,
                          sortObserved] at continued
                        exact continued.1
                    | Ok sort =>
                        simp [VcTermSortRaw.collect_sorts_loop.body, observed,
                          sortObserved] at continued
                        exact one_bind_cont_iterator_first
                          (VcTermSort.ModelVec.push sorts sort)
                          (fun updated => (updated, none))
                          advanced next (nextSorts, nextError) continued
          subst next
          exact slice_iterator_next_some_decreases iter advanced value observed

theorem require_finite_dict_entry_sorts_body_decreases
    (keySort valueSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSortRaw.require_finite_dict_entry_sorts_loop.body
      keySort valueSort iter result = .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSortRaw.require_finite_dict_entry_sorts_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.require_finite_dict_entry_sorts_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeEntry, advanced⟩ := pair
      cases maybeEntry with
      | none =>
          simp [VcTermSortRaw.require_finite_dict_entry_sorts_loop.body, observed] at continued
      | some entry =>
          obtain ⟨key, value⟩ := entry
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail error =>
                simp [VcTermSortRaw.require_finite_dict_entry_sorts_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSortRaw.require_finite_dict_entry_sorts_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
              cases isOk with
              | false =>
                  simp [VcTermSortRaw.require_finite_dict_entry_sorts_loop.body, observed,
                    isOkObserved] at continued
                  exact continued.1
              | true =>
                  simp [VcTermSortRaw.require_finite_dict_entry_sorts_loop.body, observed,
                    isOkObserved] at continued
                  simp only [Bind.bind, Std.bind] at continued
                  all_goals repeat' split at continued
                  all_goals
                    have mapped := congrArg continuationIterator continued
                    simp [continuationIterator] at mapped <;> assumption
          subst next
          exact slice_iterator_next_some_decreases iter advanced (key, value) observed

theorem validate_bound_occurrences_all_body_decreases
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter VcTermSort.Term)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSortRaw.validate_bound_occurrences.all_loop.body
      binder binderSort iter result = .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSortRaw.validate_bound_occurrences.all_loop.body, observed] at continued
  | div =>
      simp [VcTermSortRaw.validate_bound_occurrences.all_loop.body, observed] at continued
  | ok pair =>
      obtain ⟨maybeTerm, advanced⟩ := pair
      cases maybeTerm with
      | none =>
          simp [VcTermSortRaw.validate_bound_occurrences.all_loop.body, observed] at continued
      | some term =>
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail isOkError =>
                simp [VcTermSortRaw.validate_bound_occurrences.all_loop.body, observed,
                  isOkObserved] at continued
            | div =>
                simp [VcTermSortRaw.validate_bound_occurrences.all_loop.body, observed,
                  isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSortRaw.validate_bound_occurrences.all_loop.body, observed,
                      isOkObserved] at continued
                    exact continued.1
                | true =>
                    simp [VcTermSortRaw.validate_bound_occurrences.all_loop.body, observed,
                      isOkObserved] at continued
                    exact one_bind_cont_iterator_first
                      (VcTermSortRaw.validate_bound_occurrences.one term binder binderSort)
                      (fun checked => checked)
                      advanced next nextResult continued
          subst next
          exact slice_iterator_next_some_decreases iter advanced term observed

theorem validate_bound_occurrences_all_transfers_body_decreases
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body
      binder binderSort iter result = .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body,
        observed] at continued
  | div =>
      simp [VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body,
        observed] at continued
  | ok pair =>
      obtain ⟨maybeAmount, advanced⟩ := pair
      cases maybeAmount with
      | none =>
          simp [VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body,
            observed] at continued
      | some amount =>
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail isOkError =>
                simp [VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body,
                  observed, isOkObserved] at continued
            | div =>
                simp [VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body,
                  observed, isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body,
                      observed, isOkObserved] at continued
                    exact continued.1
                | true =>
                    simp [VcTermSortRaw.validate_bound_occurrences.all_transfers_loop.body,
                      observed, isOkObserved] at continued
                    exact one_bind_cont_iterator_first
                      (VcTermSortRaw.validate_bound_occurrences.one
                        amount.receiver binder binderSort)
                      (fun checked => checked)
                      advanced next nextResult continued
          subst next
          exact slice_iterator_next_some_decreases iter advanced amount observed

theorem validate_bound_occurrences_all_entries_body_decreases
    (binder : String) (binderSort : VcTermSort.Sort)
    (iter next : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
    (result nextResult : core.result.Result Unit VcTermSort.SortError)
    (continued : VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body
      binder binderSort iter result = .ok (.cont (next, nextResult))) :
    sliceIteratorRemaining next < sliceIteratorRemaining iter := by
  cases observed : core.slice.iter.IteratorSliceIter.next iter with
  | fail iteratorError =>
      simp [VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body,
        observed] at continued
  | div =>
      simp [VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body,
        observed] at continued
  | ok pair =>
      obtain ⟨maybeEntry, advanced⟩ := pair
      cases maybeEntry with
      | none =>
          simp [VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body,
            observed] at continued
      | some entry =>
          obtain ⟨key, value⟩ := entry
          have advanced_eq : advanced = next := by
            cases isOkObserved : core.result.Result.is_ok result with
            | fail isOkError =>
                simp [VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body,
                  observed, isOkObserved] at continued
            | div =>
                simp [VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body,
                  observed, isOkObserved] at continued
            | ok isOk =>
                cases isOk with
                | false =>
                    simp [VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body,
                      observed, isOkObserved] at continued
                    exact continued.1
                | true =>
                    simp [VcTermSortRaw.validate_bound_occurrences.all_entries_loop.body,
                      observed, isOkObserved] at continued
                    exact one_bind_cont_iterator_first
                      (VcTermSortRaw.validate_bound_occurrences.two
                        key value binder binderSort)
                      (fun checked => checked)
                      advanced next nextResult continued
          subst next
          exact slice_iterator_next_some_decreases iter advanced (key, value) observed

end VcTermSort.RawProofs
