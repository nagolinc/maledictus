import VcTermSortProofs.Composition

open Aeneas Aeneas.Std Result ControlFlow Error

namespace VcTermSort.Proofs

/-- The exact invariant inherited from every production Rust `Vec`: its
    recursive list representation fits in the target `usize` length. -/
def ModelVecBounded {T : Type} (values : VcTermSort.ModelVec T) : Prop :=
  values.length ≤ Usize.max

theorem model_vec_with_capacity_bounded {T : Type} (capacity : Usize) :
    ModelVecBounded (VcTermSort.ModelVec.with_capacity T capacity) := by
  simp [ModelVecBounded, VcTermSort.ModelVec.with_capacity]

theorem model_vec_with_capacity_refines {T : Type} (capacity : Usize) :
    VcTermSort.ModelVec.with_capacity T capacity =
      (alloc.vec.Vec.with_capacity T capacity).val := by
  rfl

theorem model_vec_deref_refines {T : Type}
    (values : VcTermSort.ModelVec T) (bounded : ModelVecBounded values) :
    (VcTermSort.ModelVec.deref values).val = values := by
  exact VcTermSort.ModelVec.deref_exact values bounded

theorem model_vec_len_refines {T : Type}
    (values : VcTermSort.ModelVec T) (bounded : ModelVecBounded values) :
    (VcTermSort.ModelVec.len values).val = values.length := by
  exact VcTermSort.ModelVec.len_exact values bounded

theorem model_vec_is_empty_refines {T : Type}
    (values : VcTermSort.ModelVec T) :
    VcTermSort.ModelVec.is_empty Global values = .ok values.isEmpty := by
  rfl

theorem model_vec_into_iter_refines {T : Type}
    (values : VcTermSort.ModelVec T) (bounded : ModelVecBounded values) :
    ∃ iter,
      SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
          Global values = .ok iter ∧
      iter.slice.val = values ∧ iter.i = 0 := by
  let iter : core.slice.iter.Iter T := ⟨VcTermSort.ModelVec.deref values, 0⟩
  refine ⟨iter, rfl, ?_, rfl⟩
  exact model_vec_deref_refines values bounded

theorem model_vec_push_refines {T : Type}
    (values : VcTermSort.ModelVec T) (value : T)
    (bounded : values.length < Usize.max) :
    ∃ updated,
      VcTermSort.ModelVec.push values value = .ok updated ∧
      updated = List.append (show List T from values) [value] ∧
      ModelVecBounded updated := by
  let updated := List.append (show List T from values) [value]
  refine ⟨updated, VcTermSort.ModelVec.push_exact values value bounded, rfl, ?_⟩
  simp [ModelVecBounded, updated]
  omega

theorem model_vec_push_at_capacity_refines {T : Type}
    (values : VcTermSort.ModelVec T) (value : T)
    (full : values.length = Usize.max) :
    VcTermSort.ModelVec.push values value = .fail .maximumSizeExceeded := by
  exact VcTermSort.ModelVec.push_at_capacity_fails values value full

/-- The complete reachable operation inventory for the extraction-local
    recursive list model of Rust vectors. -/
structure ModelVecRefinement : Prop where
  withCapacity : ∀ (T : Type) (capacity : Usize),
    ModelVecBounded (VcTermSort.ModelVec.with_capacity T capacity)
  withCapacityRust : ∀ (T : Type) (capacity : Usize),
    VcTermSort.ModelVec.with_capacity T capacity =
      (alloc.vec.Vec.with_capacity T capacity).val
  deref : ∀ (T : Type) (values : VcTermSort.ModelVec T),
    ModelVecBounded values → (VcTermSort.ModelVec.deref values).val = values
  len : ∀ (T : Type) (values : VcTermSort.ModelVec T),
    ModelVecBounded values → (VcTermSort.ModelVec.len values).val = values.length
  isEmpty : ∀ (T : Type) (values : VcTermSort.ModelVec T),
    VcTermSort.ModelVec.is_empty Global values = .ok values.isEmpty
  intoIter : ∀ (T : Type) (values : VcTermSort.ModelVec T),
    ModelVecBounded values → ∃ iter,
      SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
          Global values = .ok iter ∧
      iter.slice.val = values ∧ iter.i = 0
  push : ∀ (T : Type) (values : VcTermSort.ModelVec T) (value : T),
    values.length < Usize.max → ∃ updated,
      VcTermSort.ModelVec.push values value = .ok updated ∧
      updated = List.append (show List T from values) [value] ∧
      ModelVecBounded updated
  pushAtCapacity : ∀ (T : Type) (values : VcTermSort.ModelVec T) (value : T),
    values.length = Usize.max →
      VcTermSort.ModelVec.push values value = .fail .maximumSizeExceeded

theorem recursive_vec_list_refinement : ModelVecRefinement where
  withCapacity := fun _ capacity => model_vec_with_capacity_bounded capacity
  withCapacityRust := fun _ capacity => model_vec_with_capacity_refines capacity
  deref := fun _ values => model_vec_deref_refines values
  len := fun _ values => model_vec_len_refines values
  isEmpty := fun _ values => model_vec_is_empty_refines values
  intoIter := fun _ values => model_vec_into_iter_refines values
  push := fun _ values value => model_vec_push_refines values value
  pushAtCapacity := fun _ values value => model_vec_push_at_capacity_refines values value

end VcTermSort.Proofs
