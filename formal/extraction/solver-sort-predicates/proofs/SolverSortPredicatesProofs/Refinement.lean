import SolverSortPredicates

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace SolverSortPredicates.Proofs

theorem sizeOf_list_take_le (count : Nat) (values : List vc.Sort) :
    sizeOf (values.take count) <= sizeOf values := by
  induction values generalizing count <;> cases count <;> simp_all
  omega

@[simp]
theorem sizeOf_list_take_lt_succ (count : Nat) (values : List vc.Sort) :
    sizeOf (values.take count) < 1 + sizeOf values := by
  have bound := sizeOf_list_take_le count values
  omega

@[simp]
theorem sizeOf_list_take_le_add_one (count : Nat) (values : List vc.Sort) :
    sizeOf (values.take count) <= sizeOf values + 1 := by
  have bound := sizeOf_list_take_le count values
  omega

mutual

def collectionKeySpec : vc.Sort -> Bool
  | .Bool | .Int | .String | .Bytes => true
  | .Tuple elements => collectionKeyListSpec (elements.take Usize.max)
  | .VariadicTuple element => collectionKeySpec element
  | _ => false
termination_by sort => sizeOf sort

def collectionKeyListSpec : List vc.Sort -> Bool
  | [] => true
  | head :: tail => collectionKeySpec head && collectionKeyListSpec tail
termination_by sorts => sizeOf sorts
decreasing_by
  all_goals simp_wf
  all_goals omega
end

mutual

def collectionValueSpec : vc.Sort -> Bool
  | .Bool | .Int | .String | .Reference | .Bytes => true
  | .Tuple elements => collectionValueListSpec (elements.take Usize.max)
  | .VariadicTuple element | .List element => collectionValueSpec element
  | .Set element => collectionKeySpec element
  | .Dict key value | .FiniteDict key value =>
      collectionKeySpec key && collectionValueSpec value
  | _ => false
termination_by sort => sizeOf sort

def collectionValueListSpec : List vc.Sort -> Bool
  | [] => true
  | head :: tail => collectionValueSpec head && collectionValueListSpec tail
termination_by sorts => sizeOf sorts
decreasing_by
  all_goals simp_wf
  all_goals omega
end

mutual

def nestedEqualitySpec : vc.Sort -> Bool
  | .Bool | .Int | .String | .Reference | .Class | .Bytes => true
  | .Tuple elements => nestedEqualityListSpec (elements.take Usize.max)
  | .VariadicTuple element | .List element => nestedEqualitySpec element
  | _ => false
termination_by sort => sizeOf sort

def nestedEqualityListSpec : List vc.Sort -> Bool
  | [] => true
  | head :: tail => nestedEqualitySpec head && nestedEqualityListSpec tail
termination_by sorts => sizeOf sorts
decreasing_by
  all_goals simp_wf
  all_goals omega
end

def predicateLoopBody
    (predicate : vc.Sort -> Result Bool)
    (iter : core.slice.iter.Iter vc.Sort) (valid : Bool) :
    Result (ControlFlow ((core.slice.iter.Iter vc.Sort) × Bool) Bool) := do
  let (next, iterNext) <- core.slice.iter.IteratorSliceIter.next iter
  match next with
  | none => .ok (.done valid)
  | some element =>
      if valid then
        let validNext <- predicate element
        .ok (.cont (iterNext, validNext))
      else
        .ok (.cont (iterNext, false))

theorem predicate_loop_exact
    (predicate : vc.Sort -> Result Bool) (spec : vc.Sort -> Bool)
    (iter : core.slice.iter.Iter vc.Sort) (valid : Bool)
    (childrenExact : forall element,
      element ∈ iter.slice.val.drop iter.i -> predicate element = .ok (spec element)) :
    runLoopFuel (iter.slice.val.length - iter.i + 1)
        (fun state => predicateLoopBody predicate state.1 state.2) (iter, valid) =
      .ok (valid && (iter.slice.val.drop iter.i).all spec) := by
  rw [runLoopFuel]
  by_cases within : iter.i < iter.slice.len
  · have withinValues : iter.i < iter.slice.val.length := by simpa using within
    let current : vc.Sort := iter.slice.val[iter.i]
    let iterNext : core.slice.iter.Iter vc.Sort := { iter with i := iter.i + 1 }
    have nextStep :
        core.slice.iter.IteratorSliceIter.next iter =
          .ok (some current, iterNext) := by
      unfold core.slice.iter.IteratorSliceIter.next
      rw [dif_pos within]
      congr 3
    have dropStep :
        iter.slice.val.drop iter.i =
          current :: iter.slice.val.drop (iter.i + 1) := by
      simp [current]
    have childExact := childrenExact current (by
      rw [dropStep]
      exact List.mem_cons_self)
    have tailExact : forall element,
        element ∈ iter.slice.val.drop (iter.i + 1) ->
          predicate element = .ok (spec element) := by
      intro element member
      apply childrenExact element
      rw [dropStep]
      exact List.mem_cons_of_mem _ member
    have fuelEqual :
        iter.slice.val.length - iter.i =
          iter.slice.val.length - (iter.i + 1) + 1 := by
      omega
    by_cases currentlyValid : valid
    · have bodyStep : predicateLoopBody predicate iter valid =
          .ok (.cont (iterNext, spec current)) := by
        rw [predicateLoopBody, nextStep]
        simp only [bind_tc_ok, currentlyValid, if_true]
        have evaluated :
            ((do
              let validNext <- predicate current
              Result.ok (ControlFlow.cont (iterNext, validNext))) :
                Result (ControlFlow ((core.slice.iter.Iter vc.Sort) × Bool) Bool)) =
              Result.ok (ControlFlow.cont (iterNext, spec current)) := by
          rw [childExact]
          simp only [bind_tc_ok]
        exact evaluated
      rw [bodyStep]
      simp only [bind_tc_ok]
      rw [fuelEqual]
      have recursive := predicate_loop_exact predicate spec iterNext
        (spec current) (by simpa [iterNext] using tailExact)
      rw [dropStep]
      simp only [List.all_cons, currentlyValid, Bool.true_and]
      change runLoopFuel
        (iterNext.slice.val.length - iterNext.i + 1)
        (fun state => predicateLoopBody predicate state.1 state.2)
        (iterNext, spec current) =
          .ok (spec current &&
            (iterNext.slice.val.drop iterNext.i).all spec)
      exact recursive
    · have currentlyInvalid : valid = false :=
        Bool.eq_false_of_not_eq_true currentlyValid
      have bodyStep : predicateLoopBody predicate iter valid =
          .ok (.cont (iterNext, false)) := by
        rw [predicateLoopBody, nextStep]
        simp only [bind_tc_ok, currentlyInvalid, Bool.false_eq_true, if_false]
        rfl
      rw [bodyStep]
      simp only [bind_tc_ok]
      rw [fuelEqual]
      have recursive := predicate_loop_exact predicate spec iterNext false
        (by simpa [iterNext] using tailExact)
      rw [currentlyInvalid]
      simp only [Bool.false_and]
      change runLoopFuel
        (iterNext.slice.val.length - iterNext.i + 1)
        (fun state => predicateLoopBody predicate state.1 state.2)
        (iterNext, false) = .ok false
      simpa only [Bool.false_and] using recursive
  · have exhausted : iter.slice.val.length <= iter.i := by
      simpa using Nat.le_of_not_gt within
    have nextStep :
        core.slice.iter.IteratorSliceIter.next iter = .ok (none, iter) := by
      unfold core.slice.iter.IteratorSliceIter.next
      simp [exhausted]
    have bodyStep : predicateLoopBody predicate iter valid = .ok (.done valid) := by
      rw [predicateLoopBody, nextStep]
      simp only [bind_tc_ok]
      rfl
    rw [bodyStep]
    rw [List.drop_eq_nil_of_le exhausted]
    simp only [bind_tc_ok, List.all_nil, Bool.and_true]
termination_by iter.slice.val.length - iter.i
decreasing_by all_goals omega

theorem collection_key_list_all (values : List vc.Sort) :
    values.all collectionKeySpec = collectionKeyListSpec values := by
  induction values <;> simp_all [collectionKeyListSpec]

theorem collection_value_list_all (values : List vc.Sort) :
    values.all collectionValueSpec = collectionValueListSpec values := by
  induction values <;> simp_all [collectionValueListSpec]

theorem nested_equality_list_all (values : List vc.Sort) :
    values.all nestedEqualitySpec = nestedEqualityListSpec values := by
  induction values <;> simp_all [nestedEqualityListSpec]

theorem collection_key_loop_exact
    (iter : core.slice.iter.Iter vc.Sort) (valid : Bool)
    (childrenExact : forall element,
      element ∈ iter.slice.val.drop iter.i ->
        solver.is_z3_collection_key_sort element = .ok (collectionKeySpec element)) :
    solver.is_z3_collection_key_sort_loop iter valid =
      .ok (valid && (iter.slice.val.drop iter.i).all collectionKeySpec) := by
  rw [solver.is_z3_collection_key_sort_loop.eq_def]
  have bodyExact :
      (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
        solver.is_z3_collection_key_sort_loop.body state.1 state.2) =
        (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
          predicateLoopBody solver.is_z3_collection_key_sort state.1 state.2) := by
    funext state
    rcases state with ⟨iter, valid⟩
    rw [solver.is_z3_collection_key_sort_loop.body.eq_def]
    rfl
  rw [bodyExact]
  exact predicate_loop_exact _ _ _ _ childrenExact

theorem collection_value_loop_exact
    (iter : core.slice.iter.Iter vc.Sort) (valid : Bool)
    (childrenExact : forall element,
      element ∈ iter.slice.val.drop iter.i ->
        solver.is_z3_collection_value_sort element = .ok (collectionValueSpec element)) :
    solver.is_z3_collection_value_sort_loop iter valid =
      .ok (valid && (iter.slice.val.drop iter.i).all collectionValueSpec) := by
  rw [solver.is_z3_collection_value_sort_loop.eq_def]
  have bodyExact :
      (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
        solver.is_z3_collection_value_sort_loop.body state.1 state.2) =
        (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
          predicateLoopBody solver.is_z3_collection_value_sort state.1 state.2) := by
    funext state
    rcases state with ⟨iter, valid⟩
    rw [solver.is_z3_collection_value_sort_loop.body.eq_def]
    rfl
  rw [bodyExact]
  exact predicate_loop_exact _ _ _ _ childrenExact

theorem nested_equality_loop_exact
    (iter : core.slice.iter.Iter vc.Sort) (valid : Bool)
    (childrenExact : forall element,
      element ∈ iter.slice.val.drop iter.i ->
        solver.is_z3_nested_equality_sort element = .ok (nestedEqualitySpec element)) :
    solver.is_z3_nested_equality_sort_loop iter valid =
      .ok (valid && (iter.slice.val.drop iter.i).all nestedEqualitySpec) := by
  rw [solver.is_z3_nested_equality_sort_loop.eq_def]
  have bodyExact :
      (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
        solver.is_z3_nested_equality_sort_loop.body state.1 state.2) =
        (fun (state : core.slice.iter.Iter vc.Sort × Bool) =>
          predicateLoopBody solver.is_z3_nested_equality_sort state.1 state.2) := by
    funext state
    rcases state with ⟨iter, valid⟩
    rw [solver.is_z3_nested_equality_sort_loop.body.eq_def]
    rfl
  rw [bodyExact]
  exact predicate_loop_exact _ _ _ _ childrenExact

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
    solver.is_z3_collection_key_sort sort = .ok (collectionKeySpec sort) := by
  rw [solver.is_z3_collection_key_sort.eq_def]
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
    solver.is_z3_collection_value_sort sort = .ok (collectionValueSpec sort) := by
  rw [solver.is_z3_collection_value_sort.eq_def]
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
    solver.is_z3_nested_equality_sort sort = .ok (nestedEqualitySpec sort) := by
  rw [solver.is_z3_nested_equality_sort.eq_def]
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

end SolverSortPredicates.Proofs
