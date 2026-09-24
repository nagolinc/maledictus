import VcTermSortProofs.StdlibRefinement

open Aeneas Aeneas.Std Result ControlFlow Error

namespace VcTermSort.Proofs

mutual

/-- Independent structural specification of Rust's compiler-generated
    `Clone` traversal for `Sort`. Unlike the extraction model, recursive fields
    are rebuilt explicitly. -/
def compilerDerivedSortClone : VcTermSort.Sort -> VcTermSort.Sort
  | .Bool => .Bool
  | .Int => .Int
  | .Float => .Float
  | .String => .String
  | .Unit => .Unit
  | .Reference => .Reference
  | .Class => .Class
  | .Bytes => .Bytes
  | .Range => .Range
  | .Tuple values => .Tuple (compilerDerivedSortCloneList values)
  | .List value => .List (compilerDerivedSortClone value)
  | .VariadicTuple value => .VariadicTuple (compilerDerivedSortClone value)
  | .Set value => .Set (compilerDerivedSortClone value)
  | .Dict key value =>
      .Dict (compilerDerivedSortClone key) (compilerDerivedSortClone value)
  | .FiniteDict key value =>
      .FiniteDict (compilerDerivedSortClone key) (compilerDerivedSortClone value)
  | .DictKeys key => .DictKeys (compilerDerivedSortClone key)

def compilerDerivedSortCloneList : List VcTermSort.Sort -> List VcTermSort.Sort
  | [] => []
  | head :: tail => compilerDerivedSortClone head :: compilerDerivedSortCloneList tail

end

mutual

theorem compiler_derived_sort_clone_identity : forall sort : VcTermSort.Sort,
    compilerDerivedSortClone sort = sort
  | .Bool => by rfl
  | .Int => by rfl
  | .Float => by rfl
  | .String => by rfl
  | .Unit => by rfl
  | .Reference => by rfl
  | .Class => by rfl
  | .Bytes => by rfl
  | .Range => by rfl
  | .Tuple values => by
      simp [compilerDerivedSortClone, compiler_derived_sort_clone_list_identity values]
  | .List value => by
      simp [compilerDerivedSortClone, compiler_derived_sort_clone_identity value]
  | .VariadicTuple value => by
      simp [compilerDerivedSortClone, compiler_derived_sort_clone_identity value]
  | .Set value => by
      simp [compilerDerivedSortClone, compiler_derived_sort_clone_identity value]
  | .Dict key value => by
      simp [compilerDerivedSortClone, compiler_derived_sort_clone_identity key,
        compiler_derived_sort_clone_identity value]
  | .FiniteDict key value => by
      simp [compilerDerivedSortClone, compiler_derived_sort_clone_identity key,
        compiler_derived_sort_clone_identity value]
  | .DictKeys key => by
      simp [compilerDerivedSortClone, compiler_derived_sort_clone_identity key]

theorem compiler_derived_sort_clone_list_identity :
    forall values : List VcTermSort.Sort,
      compilerDerivedSortCloneList values = values
  | [] => by rfl
  | head :: tail => by
      simp [compilerDerivedSortCloneList, compiler_derived_sort_clone_identity head,
        compiler_derived_sort_clone_list_identity tail]

end

/-- A compiler-derived `PartialEq` on a pure recursive enum returns true
    exactly when the two structural values are equal. This proposition is
    independent of the extraction-local Boolean implementation. -/
def CompilerDerivedSortPartialEq (left right : VcTermSort.Sort) : Prop :=
  left = right

noncomputable def compilerDerivedSortPartialEqBool
    (left right : VcTermSort.Sort) : Bool :=
  match @Classical.decEq VcTermSort.Sort left right with
  | .isTrue _ => true
  | .isFalse _ => false

theorem sort_clone_model_refines_compiler_derive (sort : VcTermSort.Sort) :
    VcTermSort.Sort.Insts.CoreCloneClone.clone sort =
      .ok (compilerDerivedSortClone sort) := by
  rw [compiler_derived_sort_clone_identity]
  rfl

theorem sort_partial_eq_model_refines_compiler_derive
    (left right : VcTermSort.Sort) :
    VcTermSort.Sort.Insts.CoreCmpPartialEqSort.eq left right = .ok true <->
      CompilerDerivedSortPartialEq left right := by
  exact sort_partial_eq_exact left right

theorem sort_partial_eq_result_refines_compiler_derive
    (left right : VcTermSort.Sort) :
    VcTermSort.Sort.Insts.CoreCmpPartialEqSort.eq left right =
      .ok (compilerDerivedSortPartialEqBool left right) := by
  change Result.ok (VcTermSort.sortModelEqPublic left right) =
    Result.ok (compilerDerivedSortPartialEqBool left right)
  unfold compilerDerivedSortPartialEqBool
  cases decision : @Classical.decEq VcTermSort.Sort left right with
  | isTrue equal =>
    rw [(sort_model_eq_true_iff left right).mpr equal]
  | isFalse different =>
    cases observed : VcTermSort.sortModelEqPublic left right with
    | false => rfl
    | true => exact False.elim (different ((sort_model_eq_true_iff left right).mp observed))

/-- Runtime-bearing `Sort` derive operations reachable from `Term::sort`.
    Rust's `Eq` derive is a marker with no method body. `Debug` is intentionally
    excluded here because its formatter output belongs to the separately
    recorded diagnostic-format refinement obligation. -/
structure ReachableSortDerivedTraitRefinement : Prop where
  clone : forall sort : VcTermSort.Sort,
    VcTermSort.Sort.Insts.CoreCloneClone.clone sort =
      .ok (compilerDerivedSortClone sort)
  partialEq : forall left right : VcTermSort.Sort,
    VcTermSort.Sort.Insts.CoreCmpPartialEqSort.eq left right =
      .ok (compilerDerivedSortPartialEqBool left right)

theorem reachable_sort_derived_trait_refinement :
    ReachableSortDerivedTraitRefinement := {
  clone := sort_clone_model_refines_compiler_derive
  partialEq := sort_partial_eq_result_refines_compiler_derive
}

end VcTermSort.Proofs
