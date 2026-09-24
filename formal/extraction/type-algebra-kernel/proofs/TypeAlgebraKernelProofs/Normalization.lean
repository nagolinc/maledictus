import TypeAlgebraKernelProofs.Sequences

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace TypeAlgebraKernel.Proofs

open TypeAlgebraKernel
open python_type_algebra_kernel

abbrev PyType := python_type_algebra_kernel.Type
abbrev PyTypeList := python_type_algebra_kernel.TypeList

def typeListContainsReference : PyTypeList -> PyType -> Bool
  | .Empty, _ => false
  | .Item ty tail, expected =>
      typeEqReference ty expected || typeListContainsReference tail expected

theorem type_list_contains_exact (types : PyTypeList) (expected : PyType) :
    type_list_contains types expected =
      .ok (typeListContainsReference types expected) := by
  rw [type_list_contains.eq_def]
  cases types with
  | Empty => rfl
  | Item ty tail =>
      simp only [typeListContainsReference]
      rw [type_equals_exact]
      cases typeEqReference ty expected <;> simp
      exact type_list_contains_exact tail expected
termination_by typeListSize types
decreasing_by exact typeListSize_tail_lt _ _

def flattenUnionReference : PyTypeList -> PyTypeList -> PyTypeList
  | .Empty, flattened => flattened
  | .Item ty tail, flattened =>
      let next := match ty with
        | .Union nested => flattenUnionReference nested flattened
        | other =>
            if typeListContainsReference flattened other then flattened
            else .Item other flattened
      flattenUnionReference tail next
termination_by types => typeListSize types
decreasing_by
  all_goals simp_all [typeListSize, typeSize]
  all_goals omega

theorem flatten_union_types_exact (types flattened : PyTypeList) :
    flatten_union_types types flattened =
      .ok (flattenUnionReference types flattened) := by
  rw [flatten_union_types.eq_def]
  cases types with
  | Empty => simp only [flattenUnionReference]
  | Item ty tail =>
      cases ty <;> simp only [flattenUnionReference]
      all_goals try rw [type_list_contains_exact]
      all_goals try simp only [bind_tc_ok]
      all_goals try split <;> simp_all
      all_goals try exact flatten_union_types_exact tail _
      · rw [flatten_union_types_exact]
        simp only [bind_tc_ok]
        exact flatten_union_types_exact tail _
termination_by typeListSize types
decreasing_by
  all_goals simp_all [typeListSize, typeSize]
  all_goals omega

def reverseTypeListReference : PyTypeList -> PyTypeList -> PyTypeList
  | .Empty, reversed => reversed
  | .Item ty tail, reversed =>
      reverseTypeListReference tail (.Item ty reversed)

theorem reverse_type_list_exact (types reversed : PyTypeList) :
    reverse_type_list types reversed =
      .ok (reverseTypeListReference types reversed) := by
  rw [reverse_type_list.eq_def]
  cases types with
  | Empty => rfl
  | Item ty tail => exact reverse_type_list_exact tail (.Item ty reversed)
termination_by typeListSize types
decreasing_by exact typeListSize_tail_lt _ _

def normalizeTypeListReference (types : PyTypeList) : PyType :=
  let reversed := flattenUnionReference types .Empty
  let flattened := reverseTypeListReference reversed .Empty
  match flattened with
  | .Item single .Empty => single
  | other => .Union other

theorem normalize_type_list_exact (types : PyTypeList) :
    normalize_type_list types = .ok (normalizeTypeListReference types) := by
  unfold normalize_type_list
  rw [flatten_union_types_exact]
  simp only [bind_tc_ok]
  rw [reverse_type_list_exact]
  simp only [bind_tc_ok, normalizeTypeListReference]
  cases reverseTypeListReference (flattenUnionReference types .Empty) .Empty with
  | Empty => rfl
  | Item single tail =>
      cases tail <;> rfl

/-- Universal exact refinement of the production `normalize_union` entrypoint.
    `Vec`'s length proof is already part of the extracted input type. -/
theorem normalize_union_exact (types : alloc.vec.Vec PyType) :
    normalize_union types =
      .ok (normalizeTypeListReference (prependTypes types.val .Empty)) := by
  unfold normalize_union
  rw [typeList_from_vec_exact]
  simp only [bind_tc_ok]
  rw [normalize_type_list_exact]

def expandUnionListReference (ty : PyType) : PyTypeList :=
  match normalizeTypeListReference (.Item ty .Empty) with
  | .Union types => types
  | other => .Item other .Empty

theorem expand_union_list_exact (ty : PyType) :
    expand_union_list ty = .ok (expandUnionListReference ty) := by
  unfold expand_union_list
  rw [clone_type_exact]
  simp only [bind_tc_ok]
  rw [normalize_type_list_exact]
  simp only [bind_tc_ok, expandUnionListReference]
  cases normalizeTypeListReference (.Item ty .Empty) <;> rfl

/-- Universal exact refinement of `expand_union`, conditional only on the real
    representable-vector capacity enforced by Rust's `Vec`. -/
theorem expand_union_exact
    (ty : PyType)
    (bounded : (typeListToList (expandUnionListReference ty)).length <= Usize.max) :
    exists output,
      expand_union ty = .ok output /\
      output.val = typeListToList (expandUnionListReference ty) := by
  unfold expand_union
  rw [expand_union_list_exact]
  simpa only [bind_tc_ok] using
    typeList_into_vec_exact (expandUnionListReference ty) bounded

end TypeAlgebraKernel.Proofs
