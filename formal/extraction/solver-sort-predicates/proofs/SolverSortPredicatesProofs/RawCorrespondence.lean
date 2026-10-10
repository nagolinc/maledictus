import SolverSortPredicates.Code.RawFuns
import SolverSortPredicatesProofs.Refinement
import SolverSortPredicatesProofs.LoopNormalization

open Aeneas Aeneas.Std Result ControlFlow Error

namespace SolverSortPredicates.RawProofs
open SolverSortPredicates.Proofs

/-- Every continuing predicate-loop path advances the actual source iterator,
    regardless of the predicate's success, failure, or divergence behavior. -/
theorem predicate_loop_body_decreases
    (predicate : vc.Sort → Result Bool)
    (state next : core.slice.iter.Iter vc.Sort × Bool)
    (continued : predicateLoopBody predicate state.1 state.2 = .ok (.cont next)) :
    next.1.slice.val.length - next.1.i < state.1.slice.val.length - state.1.i := by
  rcases state with ⟨iter, valid⟩
  by_cases within : iter.i < iter.slice.len
  · have withinValues : iter.i < iter.slice.val.length := by simpa using within
    let current : vc.Sort := iter.slice.val[iter.i]
    let iterNext : core.slice.iter.Iter vc.Sort := { iter with i := iter.i + 1 }
    have nextStep : core.slice.iter.IteratorSliceIter.next iter =
        .ok (some current, iterNext) := by
      unfold core.slice.iter.IteratorSliceIter.next
      rw [dif_pos within]
      congr 3
    cases valid with
    | false =>
        simp only [predicateLoopBody, nextStep, bind_tc_ok, Bool.false_eq_true,
          if_false] at continued
        cases continued
        simp only [iterNext]
        omega
    | true =>
        cases checked : predicate current with
        | fail error =>
            simp [predicateLoopBody, nextStep, checked] at continued
        | div =>
            simp [predicateLoopBody, nextStep, checked] at continued
        | ok accepted =>
            simp [predicateLoopBody, nextStep, checked] at continued
            cases continued
            simp only [iterNext]
            omega
  · have exhausted : iter.slice.val.length ≤ iter.i := by
      simpa using Nat.le_of_not_gt within
    have nextStep : core.slice.iter.IteratorSliceIter.next iter = .ok (none, iter) := by
      unfold core.slice.iter.IteratorSliceIter.next
      simp [exhausted]
    simp [predicateLoopBody, nextStep] at continued

theorem raw_predicate_loop_exact
    (predicate : vc.Sort → Result Bool) (spec : vc.Sort → Bool)
    (iter : core.slice.iter.Iter vc.Sort) (valid : Bool)
    (childrenExact : ∀ element, element ∈ iter.slice.val.drop iter.i →
      predicate element = .ok (spec element)) :
    loop (fun state : core.slice.iter.Iter vc.Sort × Bool =>
      predicateLoopBody predicate state.1 state.2) (iter, valid) =
      .ok (valid && (iter.slice.val.drop iter.i).all spec) := by
  rw [partial_loop_eq_fuel_of_decreases _
    (fun state : core.slice.iter.Iter vc.Sort × Bool =>
      state.1.slice.val.length - state.1.i)
    (predicate_loop_body_decreases predicate)]
  exact predicate_loop_exact predicate spec iter valid childrenExact

theorem collection_key_loop_exact
    (iter : core.slice.iter.Iter vc.Sort) (valid : Bool)
    (childrenExact : forall element,
      element ∈ iter.slice.val.drop iter.i ->
        SolverSortPredicatesRaw.solver.is_z3_collection_key_sort element = .ok (collectionKeySpec element)) :
    SolverSortPredicatesRaw.solver.is_z3_collection_key_sort_loop iter valid =
      .ok (valid && (iter.slice.val.drop iter.i).all collectionKeySpec) := by
  rw [SolverSortPredicatesRaw.solver.is_z3_collection_key_sort_loop.eq_def]
  have bodyExact :
      (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
        SolverSortPredicatesRaw.solver.is_z3_collection_key_sort_loop.body state.1 state.2) =
        (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
          predicateLoopBody SolverSortPredicatesRaw.solver.is_z3_collection_key_sort state.1 state.2) := by
    funext state
    rcases state with ⟨iter, valid⟩
    rw [SolverSortPredicatesRaw.solver.is_z3_collection_key_sort_loop.body.eq_def]
    rfl
  rw [bodyExact]
  exact raw_predicate_loop_exact _ _ _ _ childrenExact

theorem collection_value_loop_exact
    (iter : core.slice.iter.Iter vc.Sort) (valid : Bool)
    (childrenExact : forall element,
      element ∈ iter.slice.val.drop iter.i ->
        SolverSortPredicatesRaw.solver.is_z3_collection_value_sort element = .ok (collectionValueSpec element)) :
    SolverSortPredicatesRaw.solver.is_z3_collection_value_sort_loop iter valid =
      .ok (valid && (iter.slice.val.drop iter.i).all collectionValueSpec) := by
  rw [SolverSortPredicatesRaw.solver.is_z3_collection_value_sort_loop.eq_def]
  have bodyExact :
      (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
        SolverSortPredicatesRaw.solver.is_z3_collection_value_sort_loop.body state.1 state.2) =
        (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
          predicateLoopBody SolverSortPredicatesRaw.solver.is_z3_collection_value_sort state.1 state.2) := by
    funext state
    rcases state with ⟨iter, valid⟩
    rw [SolverSortPredicatesRaw.solver.is_z3_collection_value_sort_loop.body.eq_def]
    rfl
  rw [bodyExact]
  exact raw_predicate_loop_exact _ _ _ _ childrenExact

theorem nested_equality_loop_exact
    (iter : core.slice.iter.Iter vc.Sort) (valid : Bool)
    (childrenExact : forall element,
      element ∈ iter.slice.val.drop iter.i ->
        SolverSortPredicatesRaw.solver.is_z3_nested_equality_sort element = .ok (nestedEqualitySpec element)) :
    SolverSortPredicatesRaw.solver.is_z3_nested_equality_sort_loop iter valid =
      .ok (valid && (iter.slice.val.drop iter.i).all nestedEqualitySpec) := by
  rw [SolverSortPredicatesRaw.solver.is_z3_nested_equality_sort_loop.eq_def]
  have bodyExact :
      (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
        SolverSortPredicatesRaw.solver.is_z3_nested_equality_sort_loop.body state.1 state.2) =
        (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
          predicateLoopBody SolverSortPredicatesRaw.solver.is_z3_nested_equality_sort state.1 state.2) := by
    funext state
    rcases state with ⟨iter, valid⟩
    rw [SolverSortPredicatesRaw.solver.is_z3_nested_equality_sort_loop.body.eq_def]
    rfl
  rw [bodyExact]
  exact raw_predicate_loop_exact _ _ _ _ childrenExact

theorem sizeOf_mem_list_lt {value : vc.Sort} {values : List vc.Sort}
    (member : value ∈ values) : sizeOf value < sizeOf values := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with same | member
      · subst value
        simp
        omega
      · have smaller := inductionHypothesis member
        simp
        omega

theorem sizeOf_mem_take_lt {value : vc.Sort} {values : List vc.Sort} {count : Nat}
    (member : value ∈ values.take count) : sizeOf value < 1 + sizeOf values := by
  have originalMember : value ∈ values := List.mem_of_mem_take member
  have smaller := sizeOf_mem_list_lt originalMember
  omega

mutual

theorem collection_key_sort_all_inputs_exact (sort : vc.Sort) :
    SolverSortPredicatesRaw.solver.is_z3_collection_key_sort sort = .ok (collectionKeySpec sort) := by
  rw [SolverSortPredicatesRaw.solver.is_z3_collection_key_sort.eq_def]
  cases sort with
  | Bool | Int | Float | String | Unit | Reference | Class | Bytes | Range |
      List | Set | Dict | FiniteDict | DictKeys => simp only [collectionKeySpec]
  | VariadicTuple element =>
      simp only [collectionKeySpec]
      exact collection_key_sort_all_inputs_exact element
  | Tuple elements =>
      simp only [collectionKeySpec]
      rw [shared_vec_into_iter_exact]
      simp only [bind_tc_ok]
      rw [collection_key_loop_exact]
      · simp only [Bool.true_and, collection_key_list_all]
        rfl
      · intro element member
        exact collection_key_sort_all_inputs_exact element
termination_by sizeOf sort

theorem collection_value_sort_all_inputs_exact (sort : vc.Sort) :
    SolverSortPredicatesRaw.solver.is_z3_collection_value_sort sort = .ok (collectionValueSpec sort) := by
  rw [SolverSortPredicatesRaw.solver.is_z3_collection_value_sort.eq_def]
  cases sort with
  | Bool | Int | Float | String | Unit | Reference | Class | Bytes | Range | DictKeys =>
      simp only [collectionValueSpec]
  | Tuple elements =>
      simp only [collectionValueSpec]
      rw [shared_vec_into_iter_exact]
      simp only [bind_tc_ok]
      rw [collection_value_loop_exact]
      · simp only [Bool.true_and, collection_value_list_all]
        rfl
      · intro element member
        exact collection_value_sort_all_inputs_exact element
  | VariadicTuple element | List element =>
      simp only [collectionValueSpec]
      exact collection_value_sort_all_inputs_exact element
  | Set element =>
      simp only [collectionValueSpec]
      exact collection_key_sort_all_inputs_exact element
  | Dict key value | FiniteDict key value =>
      simp only [collectionValueSpec]
      rw [collection_key_sort_all_inputs_exact key]
      simp only [bind_tc_ok]
      by_cases keyValid : collectionKeySpec key
      · simp only [keyValid, if_true]
        exact collection_value_sort_all_inputs_exact value
      · have keyInvalid := Bool.eq_false_of_not_eq_true keyValid
        simp [keyInvalid]
termination_by sizeOf sort

theorem nested_equality_sort_all_inputs_exact (sort : vc.Sort) :
    SolverSortPredicatesRaw.solver.is_z3_nested_equality_sort sort = .ok (nestedEqualitySpec sort) := by
  rw [SolverSortPredicatesRaw.solver.is_z3_nested_equality_sort.eq_def]
  cases sort with
  | Bool | Int | Float | String | Unit | Reference | Class | Bytes | Range |
      Set | Dict | FiniteDict | DictKeys => simp only [nestedEqualitySpec]
  | Tuple elements =>
      simp only [nestedEqualitySpec]
      rw [shared_vec_into_iter_exact]
      simp only [bind_tc_ok]
      rw [nested_equality_loop_exact]
      · simp only [Bool.true_and, nested_equality_list_all]
        rfl
      · intro element member
        exact nested_equality_sort_all_inputs_exact element
  | VariadicTuple element | List element =>
      simp only [nestedEqualitySpec]
      exact nested_equality_sort_all_inputs_exact element
termination_by sizeOf sort
decreasing_by
  all_goals simp_wf
  all_goals exact sizeOf_mem_take_lt member

end


theorem collection_key_raw_eq_normalized (sort : vc.Sort) :
    SolverSortPredicatesRaw.solver.is_z3_collection_key_sort sort =
      SolverSortPredicates.solver.is_z3_collection_key_sort sort := by
  rw [collection_key_sort_all_inputs_exact,
    SolverSortPredicates.Proofs.collection_key_sort_all_inputs_exact]

theorem collection_value_raw_eq_normalized (sort : vc.Sort) :
    SolverSortPredicatesRaw.solver.is_z3_collection_value_sort sort =
      SolverSortPredicates.solver.is_z3_collection_value_sort sort := by
  rw [collection_value_sort_all_inputs_exact,
    SolverSortPredicates.Proofs.collection_value_sort_all_inputs_exact]

theorem nested_equality_raw_eq_normalized (sort : vc.Sort) :
    SolverSortPredicatesRaw.solver.is_z3_nested_equality_sort sort =
      SolverSortPredicates.solver.is_z3_nested_equality_sort sort := by
  rw [nested_equality_sort_all_inputs_exact,
    SolverSortPredicates.Proofs.nested_equality_sort_all_inputs_exact]

end SolverSortPredicates.RawProofs
