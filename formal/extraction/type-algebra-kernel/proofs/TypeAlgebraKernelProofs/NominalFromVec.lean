import TypeAlgebraNominal.Code.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace TypeAlgebraKernel.Proofs

open TypeAlgebraNominal
open TypeAlgebraNominal.python_type_algebra_kernel

def prependNominalClasses :
    List NominalClass → NominalClassList → NominalClassList :=
  fun values tail => values.foldr NominalClassList.Item tail

theorem nominalClassList_from_vec_loop_exact
    (values : List NominalClass)
    (bounded : values.length ≤ Usize.max)
    (result : NominalClassList) :
    NominalClassList.from_vec_loop
        ({ val := values, property := bounded } : alloc.vec.Vec NominalClass)
        result = .ok (prependNominalClasses values result) := by
  induction values using List.reverseRecOn generalizing result with
  | nil =>
      rw [NominalClassList.from_vec_loop.eq_def, loop.eq_def]
      simp [NominalClassList.from_vec_loop.body,
        alloc.vec.Vec.pop, prependNominalClasses]
  | append_singleton items finalClass induction =>
      rw [NominalClassList.from_vec_loop.eq_def, loop.eq_def]
      simp only
      have itemsBounded : items.length ≤ Usize.max := by
        have shorter : items.length ≤ (items ++ [finalClass]).length := by simp
        exact shorter.trans bounded
      have popped :
          alloc.vec.Vec.pop Global
              ({ val := items ++ [finalClass], property := bounded } :
                alloc.vec.Vec NominalClass) =
            .ok (some finalClass,
              ({ val := items, property := itemsBounded } :
                alloc.vec.Vec NominalClass)) := by
        unfold alloc.vec.Vec.pop
        simp
      rw [NominalClassList.from_vec_loop.body, popped]
      simp only [bind_tc_ok]
      have recursive := induction itemsBounded (.Item finalClass result)
      simpa [NominalClassList.from_vec_loop, prependNominalClasses,
        List.foldr_append] using recursive

theorem nominalClassList_from_vec_exact
    (classes : alloc.vec.Vec NominalClass) :
    NominalClassList.from_vec classes =
      .ok (prependNominalClasses classes.val .Empty) := by
  exact nominalClassList_from_vec_loop_exact
    classes.val classes.property .Empty

end TypeAlgebraKernel.Proofs
