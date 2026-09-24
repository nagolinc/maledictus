import TypeAlgebraKernelProofs.Foundation

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace TypeAlgebraKernel.Proofs

open TypeAlgebraKernel
open python_type_algebra_kernel

def typeListToList : python_type_algebra_kernel.TypeList ->
    List python_type_algebra_kernel.Type
  | .Empty => []
  | .Item ty tail => ty :: typeListToList tail

def prependTypes :
    List python_type_algebra_kernel.Type ->
    python_type_algebra_kernel.TypeList ->
    python_type_algebra_kernel.TypeList :=
  fun values tail => values.foldr python_type_algebra_kernel.TypeList.Item tail

theorem typeListToList_length_tail_lt (ty tail) :
    (typeListToList tail).length <
      (typeListToList (.Item ty tail)).length := by simp [typeListToList]

theorem vec_push_exact
    (values : alloc.vec.Vec python_type_algebra_kernel.Type)
    (value : python_type_algebra_kernel.Type)
    (space : values.val.length < Usize.max) :
    exists output,
      alloc.vec.Vec.push values value = .ok output /\
      output.val = values.val ++ [value] := by
  let output : alloc.vec.Vec python_type_algebra_kernel.Type := {
    val := values.val ++ [value]
    property := by simp; omega
  }
  refine Exists.intro output (And.intro ?_ rfl)
  unfold alloc.vec.Vec.push
  simp [output, space]

/-- Exact all-input refinement and termination of the Vec-to-TypeList loop.
    The source pops from the end and prepends, preserving the original order. -/
theorem typeList_from_vec_loop_exact
    (values : List python_type_algebra_kernel.Type)
    (bounded : values.length <= Usize.max)
    (result : python_type_algebra_kernel.TypeList) :
    python_type_algebra_kernel.TypeList.from_vec_loop
        ({ val := values, property := bounded } :
          alloc.vec.Vec python_type_algebra_kernel.Type)
        result = .ok (prependTypes values result) := by
  induction values using List.reverseRecOn generalizing result with
  | nil =>
      rw [python_type_algebra_kernel.TypeList.from_vec_loop.eq_def, loop.eq_def]
      simp [python_type_algebra_kernel.TypeList.from_vec_loop.body,
        alloc.vec.Vec.pop, prependTypes]
  | append_singleton items finalType induction =>
      rw [python_type_algebra_kernel.TypeList.from_vec_loop.eq_def, loop.eq_def]
      simp only
      have itemsBounded : items.length <= Usize.max := by
        have shorter : items.length <= (items ++ [finalType]).length := by simp
        exact shorter.trans bounded
      have popped :
          alloc.vec.Vec.pop Global
              ({ val := items ++ [finalType], property := bounded } :
                alloc.vec.Vec python_type_algebra_kernel.Type) =
            .ok (some finalType,
              ({ val := items, property := itemsBounded } :
                alloc.vec.Vec python_type_algebra_kernel.Type)) := by
        unfold alloc.vec.Vec.pop
        simp
      rw [python_type_algebra_kernel.TypeList.from_vec_loop.body, popped]
      simp only [bind_tc_ok]
      have recursive := induction itemsBounded (.Item finalType result)
      simpa [python_type_algebra_kernel.TypeList.from_vec_loop, prependTypes,
        List.foldr_append] using recursive

theorem typeList_from_vec_exact
    (types : alloc.vec.Vec python_type_algebra_kernel.Type) :
    python_type_algebra_kernel.TypeList.from_vec types =
      .ok (prependTypes types.val .Empty) := by
  exact typeList_from_vec_loop_exact types.val types.property .Empty

/-- Exact all-input refinement of the extracted source-owned TypeList-to-Vec
    traversal under the real representable-vector capacity condition. -/
theorem typeList_into_vec_loop_exact
    (types : python_type_algebra_kernel.TypeList)
    (result : alloc.vec.Vec python_type_algebra_kernel.Type)
    (bounded : result.val.length + (typeListToList types).length <= Usize.max) :
    exists output,
      python_type_algebra_kernel.TypeList.into_vec_loop types result = .ok output /\
      output.val = result.val ++ typeListToList types := by
  rw [python_type_algebra_kernel.TypeList.into_vec_loop, loop.eq_def]
  cases types with
  | Empty =>
      simp [python_type_algebra_kernel.TypeList.into_vec_loop.body,
        typeListToList]
  | Item ty tail =>
      simp only
      have space : result.val.length < Usize.max := by
        simp [typeListToList] at bounded
        omega
      obtain ⟨extended, pushed, extendedValues⟩ := vec_push_exact result ty space
      rw [python_type_algebra_kernel.TypeList.into_vec_loop.body, pushed]
      simp only [bind_tc_ok]
      have tailBounded :
          extended.val.length + (typeListToList tail).length <= Usize.max := by
        rw [extendedValues]
        simp [typeListToList] at bounded
        simp
        omega
      obtain ⟨output, traversed, outputValues⟩ :=
        typeList_into_vec_loop_exact tail extended tailBounded
      refine Exists.intro output (And.intro traversed ?_)
      rw [outputValues, extendedValues]
      simp [typeListToList, List.append_assoc]
termination_by (typeListToList types).length
decreasing_by
  simp_all [typeListToList]

theorem typeList_into_vec_exact
    (types : python_type_algebra_kernel.TypeList)
    (bounded : (typeListToList types).length <= Usize.max) :
    exists output,
      python_type_algebra_kernel.TypeList.into_vec types = .ok output /\
      output.val = typeListToList types := by
  have loop := typeList_into_vec_loop_exact types
    (alloc.vec.Vec.new python_type_algebra_kernel.Type) (by simpa using bounded)
  simpa [python_type_algebra_kernel.TypeList.into_vec] using loop

def typeListIntoVecReference
    (types : python_type_algebra_kernel.TypeList) :
    Result (alloc.vec.Vec python_type_algebra_kernel.Type) :=
  if bounded : (typeListToList types).length <= Usize.max then
    .ok { val := typeListToList types, property := bounded }
  else
    .fail .maximumSizeExceeded

theorem typeList_into_vec_loop_overflow
    (types : python_type_algebra_kernel.TypeList)
    (result : alloc.vec.Vec python_type_algebra_kernel.Type)
    (overflow : Usize.max <
      result.val.length + (typeListToList types).length) :
    python_type_algebra_kernel.TypeList.into_vec_loop types result =
      .fail .maximumSizeExceeded := by
  rw [python_type_algebra_kernel.TypeList.into_vec_loop, loop.eq_def]
  cases types with
  | Empty =>
      have withinCapacity := result.property
      simp [typeListToList] at overflow
      omega
  | Item ty tail =>
      simp only
      by_cases space : result.val.length < Usize.max
      · obtain ⟨extended, pushed, extendedValues⟩ := vec_push_exact result ty space
        rw [python_type_algebra_kernel.TypeList.into_vec_loop.body, pushed]
        simp only [bind_tc_ok]
        apply typeList_into_vec_loop_overflow tail extended
        rw [extendedValues]
        simp [typeListToList] at overflow ⊢
        omega
      · rw [python_type_algebra_kernel.TypeList.into_vec_loop.body]
        have full : result.val.length = Usize.max := by
          have withinCapacity := result.property
          omega
        have notBelowU32 : Not (Usize.max < U32.max) := by
          rcases Usize.bounds_eq with usize32 | usize64
          · omega
          · rw [usize64]
            scalar_tac
        unfold alloc.vec.Vec.push
        simp [full, notBelowU32]
termination_by (typeListToList types).length
decreasing_by
  simp_all [typeListToList]

/-- Universal exact refinement of the source-owned TypeList-to-Vec traversal.
    Unlike the success-only lemma, this theorem also characterizes the real
    `Vec` maximum-size failure for arbitrary extracted inputs. -/
theorem typeList_into_vec_all_inputs_exact
    (types : python_type_algebra_kernel.TypeList) :
    python_type_algebra_kernel.TypeList.into_vec types =
      typeListIntoVecReference types := by
  by_cases bounded : (typeListToList types).length <= Usize.max
  · obtain ⟨output, traversed, outputValues⟩ :=
      typeList_into_vec_exact types bounded
    rw [traversed]
    unfold typeListIntoVecReference
    rw [dif_pos bounded]
    congr 1
    cases output
    simp_all
  · have overflow : Usize.max < (typeListToList types).length := by omega
    unfold python_type_algebra_kernel.TypeList.into_vec
    rw [typeList_into_vec_loop_overflow types
      (alloc.vec.Vec.new python_type_algebra_kernel.Type) (by simpa using overflow)]
    unfold typeListIntoVecReference
    rw [dif_neg bounded]

end TypeAlgebraKernel.Proofs
