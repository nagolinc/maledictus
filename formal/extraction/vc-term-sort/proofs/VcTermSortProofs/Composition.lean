import VcTermSortProofs.ConcreteLoops

open Aeneas Aeneas.Std Result ControlFlow Error

namespace VcTermSort.Proofs

/-- One source-bound proof object containing the bounded exact-wrapper result
    for every normalized slice loop reachable from `Term.sort`. This composes
    the fifteen local bounds, but does not assert normalization correspondence
    or an all-input relation to production Rust. -/
structure ConcreteLoopBounds : Prop where
  allListElementSorts : ∀
      (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_list_element_sorts_loop.body
          state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.all_list_element_sorts_loop iter result = output
  allFiniteDictKeySorts : ∀
      (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_finite_dict_key_sorts_loop.body
          state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.all_finite_dict_key_sorts_loop iter result = output
  allFiniteDictValueSorts : ∀
      (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_finite_dict_value_sorts_loop.body
          state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.all_finite_dict_value_sorts_loop iter result = output
  requireVariadicTupleElementSorts : ∀
      (iter : core.slice.iter.Iter VcTermSort.Term)
      (expected : VcTermSort.Sort)
      (result : core.result.Result Unit VcTermSort.SortError),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.require_variadic_tuple_element_sorts_loop.body
          expected state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.require_variadic_tuple_element_sorts_loop
        iter expected result = output
  allNominalReferences : ∀
      (iter : core.slice.iter.Iter VcTermSort.Term) (result : Bool),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_nominal_references_loop.body state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.all_nominal_references_loop iter result = output
  allNominalReferenceKeys : ∀
      (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
      (result : Bool),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.all_nominal_reference_keys_loop.body state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.all_nominal_reference_keys_loop iter result = output
  validateIntEnumDescriptor : ∀
      (iter : core.slice.iter.Iter (String × Std.I64))
      (names : alloc.collections.btree.set.BTreeSet String Global)
      (values : alloc.collections.btree.set.BTreeSet Std.I64 Global)
      (valid : Bool),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.validate_int_enum_descriptor_loop.body
          state.1 state.2.1 state.2.2.1 state.2.2.2)
        steps (iter, names, values, valid) output ∧
      VcTermSort.validate_int_enum_descriptor_loop iter names values valid = output
  requirePredicateArgumentSorts : ∀
      (iter : core.slice.iter.Iter VcTermSort.Term)
      (result : core.result.Result Unit VcTermSort.SortError),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.require_predicate_argument_sorts_loop.body
          state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.require_predicate_argument_sorts_loop iter result = output
  requirePermissionTransferAmounts : ∀
      (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
      (result : core.result.Result Unit VcTermSort.SortError),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.require_permission_transfer_amounts_loop.body
          state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.require_permission_transfer_amounts_loop iter result = output
  requireAllSorts : ∀
      (iter : core.slice.iter.Iter VcTermSort.Term)
      (expected : VcTermSort.Sort) (context : VcTermSort.SortContext)
      (result : core.result.Result Unit VcTermSort.SortError),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.require_all_sorts_loop.body
          expected context state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.require_all_sorts_loop iter expected context result = output
  collectSorts : ∀
      (iter : core.slice.iter.Iter VcTermSort.Term)
      (sorts : VcTermSort.ModelVec VcTermSort.Sort) (error : Option VcTermSort.SortError),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.collect_sorts_loop.body
          state.1 state.2.1 state.2.2)
        steps (iter, sorts, error) output ∧
      VcTermSort.collect_sorts_loop iter sorts error = output
  requireFiniteDictEntrySorts : ∀
      (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
      (keySort valueSort : VcTermSort.Sort)
      (result : core.result.Result Unit VcTermSort.SortError),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.require_finite_dict_entry_sorts_loop.body
          keySort valueSort state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.require_finite_dict_entry_sorts_loop
        iter keySort valueSort result = output
  validateBoundOccurrencesAll : ∀
      (iter : core.slice.iter.Iter VcTermSort.Term)
      (binder : String) (binderSort : VcTermSort.Sort)
      (result : core.result.Result Unit VcTermSort.SortError),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.validate_bound_occurrences.all_loop.body
          binder binderSort state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.validate_bound_occurrences.all_loop
        iter binder binderSort result = output
  validateBoundOccurrencesAllTransfers : ∀
      (iter : core.slice.iter.Iter VcTermSort.PermissionTransferAmount)
      (binder : String) (binderSort : VcTermSort.Sort)
      (result : core.result.Result Unit VcTermSort.SortError),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.validate_bound_occurrences.all_transfers_loop.body
          binder binderSort state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.validate_bound_occurrences.all_transfers_loop
        iter binder binderSort result = output
  validateBoundOccurrencesAllEntries : ∀
      (iter : core.slice.iter.Iter (VcTermSort.Term × VcTermSort.Term))
      (binder : String) (binderSort : VcTermSort.Sort)
      (result : core.result.Result Unit VcTermSort.SortError),
    ∃ steps output,
      steps ≤ sliceIteratorRemaining iter + 1 ∧
      FiniteLoopTrace
        (fun state => VcTermSort.validate_bound_occurrences.all_entries_loop.body
          binder binderSort state.1 state.2)
        steps (iter, result) output ∧
      VcTermSort.validate_bound_occurrences.all_entries_loop
        iter binder binderSort result = output

theorem concrete_loop_bounds_composed : ConcreteLoopBounds where
  allListElementSorts := all_list_element_sorts_loop_bound
  allFiniteDictKeySorts := all_finite_dict_key_sorts_loop_bound
  allFiniteDictValueSorts := all_finite_dict_value_sorts_loop_bound
  requireVariadicTupleElementSorts :=
    require_variadic_tuple_element_sorts_loop_bound
  allNominalReferences := all_nominal_references_loop_bound
  allNominalReferenceKeys := all_nominal_reference_keys_loop_bound
  validateIntEnumDescriptor := validate_int_enum_descriptor_loop_bound
  requirePredicateArgumentSorts := require_predicate_argument_sorts_loop_bound
  requirePermissionTransferAmounts := require_permission_transfer_amounts_loop_bound
  requireAllSorts := require_all_sorts_loop_bound
  collectSorts := collect_sorts_loop_bound
  requireFiniteDictEntrySorts := require_finite_dict_entry_sorts_loop_bound
  validateBoundOccurrencesAll := validate_bound_occurrences_all_loop_bound
  validateBoundOccurrencesAllTransfers :=
    validate_bound_occurrences_all_transfers_loop_bound
  validateBoundOccurrencesAllEntries :=
    validate_bound_occurrences_all_entries_loop_bound

/-- The finite-loop-runner obligation for the normalized extraction. Each
    field uses the exact generated body, proves one source-iterator advance for
    every continuation, derives sufficient fuel, and equates the wrapper with
    the retained success, failure, or divergence trace result. -/
theorem finite_loop_runner_refinement : ConcreteLoopBounds :=
  concrete_loop_bounds_composed

end VcTermSort.Proofs
