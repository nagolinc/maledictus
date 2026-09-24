import TypeAlgebraKernel

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace TypeAlgebraKernel.Proofs

open TypeAlgebraKernel
open python_type_algebra_kernel

mutual
  @[simp] def typeSize : python_type_algebra_kernel.Type -> Nat
    | .Int => 1
    | .Bool => 1
    | .Str => 1
    | .None => 1
    | .Object => 1
    | .Class _ => 1
    | .List element => typeSize element + 1
    | .Set element => typeSize element + 1
    | .Dict key value => typeSize key + typeSize value + 1
    | .FixedTuple elements => typeListSize elements + 1
    | .VariadicTuple element => typeSize element + 1
    | .Union elements => typeListSize elements + 1

  @[simp] def typeListSize : python_type_algebra_kernel.TypeList -> Nat
    | .Empty => 1
    | .Item ty tail => typeSize ty + typeListSize tail + 1
end

theorem typeSize_list_child_lt (element : python_type_algebra_kernel.Type) :
    typeSize element < typeSize (.List element) := by simp

theorem typeSize_set_child_lt (element : python_type_algebra_kernel.Type) :
    typeSize element < typeSize (.Set element) := by simp

theorem typeSize_dict_key_lt
    (key value : python_type_algebra_kernel.Type) :
    typeSize key < typeSize (.Dict key value) := by simp

theorem typeSize_dict_value_lt
    (key value : python_type_algebra_kernel.Type) :
    typeSize value < typeSize (.Dict key value) := by simp

theorem typeSize_fixed_elements_lt
    (elements : python_type_algebra_kernel.TypeList) :
    typeListSize elements < typeSize (.FixedTuple elements) := by simp

theorem typeSize_variadic_child_lt (element : python_type_algebra_kernel.Type) :
    typeSize element < typeSize (.VariadicTuple element) := by simp

theorem typeSize_union_elements_lt
    (elements : python_type_algebra_kernel.TypeList) :
    typeListSize elements < typeSize (.Union elements) := by simp

theorem typeListSize_head_lt
    (ty : python_type_algebra_kernel.Type)
    (tail : python_type_algebra_kernel.TypeList) :
    typeSize ty < typeListSize (.Item ty tail) := by simp

theorem typeListSize_tail_lt
    (ty : python_type_algebra_kernel.Type)
    (tail : python_type_algebra_kernel.TypeList) :
    typeListSize tail < typeListSize (.Item ty tail) := by simp

theorem pairSize_list_lt
    (left right : python_type_algebra_kernel.Type) :
    typeSize left + typeSize right <
      typeSize (.List left) + typeSize (.List right) := by
  simp
  omega

theorem pairSize_set_lt
    (left right : python_type_algebra_kernel.Type) :
    typeSize left + typeSize right <
      typeSize (.Set left) + typeSize (.Set right) := by
  simp
  omega

theorem pairSize_dict_keys_lt
    (leftKey leftValue rightKey rightValue : python_type_algebra_kernel.Type) :
    typeSize leftKey + typeSize rightKey <
      typeSize (.Dict leftKey leftValue) + typeSize (.Dict rightKey rightValue) := by
  simp
  omega

theorem pairSize_dict_values_lt
    (leftKey leftValue rightKey rightValue : python_type_algebra_kernel.Type) :
    typeSize leftValue + typeSize rightValue <
      typeSize (.Dict leftKey leftValue) + typeSize (.Dict rightKey rightValue) := by
  simp
  omega

theorem pairSize_fixed_lt
    (left right : python_type_algebra_kernel.TypeList) :
    typeListSize left + typeListSize right <
      typeSize (.FixedTuple left) + typeSize (.FixedTuple right) := by
  simp
  omega

theorem pairSize_variadic_lt
    (left right : python_type_algebra_kernel.Type) :
    typeSize left + typeSize right <
      typeSize (.VariadicTuple left) + typeSize (.VariadicTuple right) := by
  simp
  omega

theorem pairSize_union_lt
    (left right : python_type_algebra_kernel.TypeList) :
    typeListSize left + typeListSize right <
      typeSize (.Union left) + typeSize (.Union right) := by
  simp
  omega

theorem pairListSize_heads_lt
    (left leftTail right rightTail) :
    typeSize left + typeSize right <
      typeListSize (.Item left leftTail) + typeListSize (.Item right rightTail) := by
  simp
  omega

theorem pairListSize_tails_lt
    (left leftTail right rightTail) :
    typeListSize leftTail + typeListSize rightTail <
      typeListSize (.Item left leftTail) + typeListSize (.Item right rightTail) := by
  simp
  omega

mutual
  def typeEqReference :
      python_type_algebra_kernel.Type -> python_type_algebra_kernel.Type -> Bool
    | .Int, .Int | .Bool, .Bool | .Str, .Str | .None, .None | .Object, .Object => true
    | .Class left, .Class right => left == right
    | .List left, .List right
    | .Set left, .Set right
    | .VariadicTuple left, .VariadicTuple right => typeEqReference left right
    | .Dict leftKey leftValue, .Dict rightKey rightValue =>
        typeEqReference leftKey rightKey && typeEqReference leftValue rightValue
    | .FixedTuple left, .FixedTuple right
    | .Union left, .Union right => typeListEqReference left right
    | _, _ => false

  def typeListEqReference :
      python_type_algebra_kernel.TypeList ->
      python_type_algebra_kernel.TypeList -> Bool
    | .Empty, .Empty => true
    | .Item left leftTail, .Item right rightTail =>
        typeEqReference left right && typeListEqReference leftTail rightTail
    | _, _ => false
end

mutual
  theorem clone_type_exact (ty : python_type_algebra_kernel.Type) :
      clone_type ty = .ok ty := by
    rw [clone_type.eq_def]
    cases ty with
    | Int | Bool | Str | None | Object => rfl
    | Class className =>
        simp [alloc.string.String.Insts.CoreCloneClone.clone]
    | List element =>
        simp only
        rw [clone_type_exact element]
        rfl
    | Set element =>
        simp only
        rw [clone_type_exact element]
        rfl
    | VariadicTuple element =>
        simp only
        rw [clone_type_exact element]
        rfl
    | Dict key value =>
        simp only
        rw [clone_type_exact key, clone_type_exact value]
        rfl
    | FixedTuple elements =>
        simp only
        rw [clone_type_list_exact elements]
        rfl
    | Union elements =>
        simp only
        rw [clone_type_list_exact elements]
        rfl
  termination_by typeSize ty
  decreasing_by
    simp_wf
    all_goals first
      | exact typeSize_list_child_lt _
      | exact typeSize_set_child_lt _
      | exact typeSize_dict_key_lt _ _
      | exact typeSize_dict_value_lt _ _
      | exact typeSize_fixed_elements_lt _

  theorem clone_type_list_exact (types : python_type_algebra_kernel.TypeList) :
      clone_type_list types = .ok types := by
    rw [clone_type_list.eq_def]
    cases types with
    | Empty => rfl
    | Item ty tail =>
        simp only
        rw [clone_type_exact ty, clone_type_list_exact tail]
        rfl
  termination_by typeListSize types
  decreasing_by
    simp_wf
    all_goals first
      | exact typeListSize_head_lt _ _
      | exact typeListSize_tail_lt _ _
end

mutual
  theorem type_equals_exact
      (left right : python_type_algebra_kernel.Type) :
      type_equals left right = .ok (typeEqReference left right) := by
    rw [type_equals.eq_def]
    cases left <;> cases right <;>
      simp only [typeEqReference, alloc.string.String.Insts.CoreCmpPartialEqString.eq]
    all_goals try rw [type_equals_exact]
    all_goals try rw [type_lists_equal_exact]
    all_goals try simp only [bind_tc_ok]
    all_goals try split <;> simp_all
    all_goals try rw [type_equals_exact]
  termination_by typeSize left + typeSize right
  decreasing_by
    simp_wf
    all_goals first
      | exact pairSize_list_lt _ _
      | exact pairSize_set_lt _ _
      | exact pairSize_dict_keys_lt _ _ _ _
      | exact pairSize_dict_values_lt _ _ _ _
      | exact pairSize_fixed_lt _ _

  theorem type_lists_equal_exact
      (left right : python_type_algebra_kernel.TypeList) :
      type_lists_equal left right = .ok (typeListEqReference left right) := by
    rw [type_lists_equal.eq_def]
    cases left <;> cases right <;> simp only [typeListEqReference]
    rw [type_equals_exact]
    cases typeEqReference _ _ <;> simp
    rw [type_lists_equal_exact]
  termination_by typeListSize left + typeListSize right
  decreasing_by
    simp_wf
    all_goals first
      | exact pairListSize_heads_lt _ _ _ _
      | exact pairListSize_tails_lt _ _ _ _
end

end TypeAlgebraKernel.Proofs
