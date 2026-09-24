import VcTermSortProofs.VecRefinement

open Aeneas Aeneas.Std Result ControlFlow Error

namespace VcTermSort.Proofs

theorem must_use_refines {T : Type} (value : T) :
    core.hint.must_use value = .ok value := by
  rfl

theorem shared_gt_refines {A B : Type} (inst : core.cmp.PartialOrd A B)
    (left : A) (right : B) :
    Shared1A.Insts.CoreCmpPartialOrdShared0B.gt inst left right =
      inst.gt left right := by
  rfl

theorem option_ok_or_else_some_refines {T E F : Type}
    (inst : core.ops.function.FnOnce F Unit E) (value : T) (fallback : F) :
    core.option.Option.ok_or_else inst (some value) fallback =
      .ok (.Ok value) := by
  rfl

theorem option_ok_or_else_none_refines {T E F : Type}
    (inst : core.ops.function.FnOnce F Unit E) (fallback : F)
    (error : E) (called : inst.call_once fallback () = .ok error) :
    core.option.Option.ok_or_else inst (none : Option T) fallback =
      .ok (core.result.Result.Err error : core.result.Result T E) := by
  simp [core.option.Option.ok_or_else, called]

theorem option_cloned_none_refines {T : Type} (inst : core.clone.Clone T) :
    core.option.OptionShared0T.cloned inst none = .ok none := by
  rfl

theorem option_cloned_some_refines {T : Type} (inst : core.clone.Clone T)
    (value cloned : T) (observed : inst.clone value = .ok cloned) :
    core.option.OptionShared0T.cloned inst (some value) = .ok (some cloned) := by
  simp [core.option.OptionShared0T.cloned, observed]

theorem box_ne_refines {T : Type} (A : Type)
    (inst : core.cmp.PartialEq T T) (left right : T) :
    Box.Insts.CoreCmpPartialEqBox.ne A inst left right = inst.ne left right := by
  rfl

theorem box_as_ref_refines {T : Type} (A : Type) (value : T) :
    Box.Insts.CoreConvertAsRef.as_ref A value = .ok value := by
  rfl

theorem btree_set_new_refines (T : Type) :
    alloc.collections.btree.set.BTreeSetTGlobal.new T = .ok [] := by
  rfl

theorem btree_set_insert_refines {T A : Type} (cloneAllocator : core.clone.Clone A)
    (ord : core.cmp.Ord T) (values : alloc.collections.btree.set.BTreeSet T A)
    (value : T) (present : Bool)
    (observed : List.anyM
      (fun existing => ord.eqInst.partialEqInst.eq existing value) values = .ok present) :
    alloc.collections.btree.set.BTreeSet.insert cloneAllocator ord values value =
      .ok (!present, if present then values else value :: values) := by
  simp [alloc.collections.btree.set.BTreeSet.insert, observed]

theorem str_to_owned_total (value : Str) :
    exists owned,
      Str.Insts.AllocBorrowToOwnedString.to_owned value = .ok owned := by
  simp [Str.Insts.AllocBorrowToOwnedString.to_owned]

theorem string_eq_refines (left right : String) :
    alloc.string.String.Insts.CoreCmpPartialEqString.eq left right =
      .ok (left == right) := by
  rfl

theorem string_partial_cmp_refines (left right : String) :
    alloc.string.String.Insts.CoreCmpPartialOrdString.partial_cmp left right =
      .ok (some (compare left right)) := by
  rfl

theorem string_cmp_refines (left right : String) :
    alloc.string.String.Insts.CoreCmpOrd.cmp left right =
      .ok (compare left right) := by
  rfl

theorem string_is_empty_refines (value : String) :
    alloc.string.String.is_empty value = .ok value.isEmpty := by
  rfl

theorem string_clone_refines (value : String) :
    alloc.string.String.Insts.CoreCloneClone.clone value = .ok value := by
  rfl

theorem slice_iterator_next_within_refines {T : Type}
    (iter : core.slice.iter.Iter T) (within : iter.i < iter.slice.len) :
    exists value next,
      core.slice.iter.IteratorSliceIter.next iter = .ok (some value, next) /\
      next.slice = iter.slice /\ next.i = iter.i + 1 := by
  have within' : iter.i < iter.slice.val.length := by simpa using within
  unfold core.slice.iter.IteratorSliceIter.next
  simp [within']

theorem slice_iterator_next_exhausted_refines {T : Type}
    (iter : core.slice.iter.Iter T) (exhausted : ¬ iter.i < iter.slice.len) :
    core.slice.iter.IteratorSliceIter.next iter = .ok (none, iter) := by
  have exhausted' : ¬ iter.i < iter.slice.val.length := by simpa using exhausted
  unfold core.slice.iter.IteratorSliceIter.next
  simp [exhausted']

/-- Complete inventory of reachable, non-formatting standard-library models in
    the extracted `Term::sort` closure. Callback-parametric operations retain
    their callback result as a premise; this proves that the wrapper adds no
    failure or divergence of its own without pretending arbitrary callbacks
    are total. `Sort` derived traits and diagnostic formatting remain separate
    recorded obligations. -/
structure ReachableStandardLibraryRefinement : Prop where
  mustUse : forall {T : Type} (value : T), core.hint.must_use value = .ok value
  sharedGt : forall {A B : Type} (inst : core.cmp.PartialOrd A B) (left : A) (right : B),
    Shared1A.Insts.CoreCmpPartialOrdShared0B.gt inst left right = inst.gt left right
  optionSome : forall {T E F : Type} (inst : core.ops.function.FnOnce F Unit E)
    (value : T) (fallback : F),
    core.option.Option.ok_or_else inst (some value) fallback = .ok (.Ok value)
  optionNone : forall {T E F : Type} (inst : core.ops.function.FnOnce F Unit E)
    (fallback : F) (error : E), inst.call_once fallback () = .ok error ->
    core.option.Option.ok_or_else inst (none : Option T) fallback =
      .ok (core.result.Result.Err error : core.result.Result T E)
  cloneNone : forall {T : Type} (inst : core.clone.Clone T),
    core.option.OptionShared0T.cloned inst none = .ok none
  cloneSome : forall {T : Type} (inst : core.clone.Clone T) (value cloned : T),
    inst.clone value = .ok cloned ->
      core.option.OptionShared0T.cloned inst (some value) = .ok (some cloned)
  boxNe : forall {T : Type} (A : Type) (inst : core.cmp.PartialEq T T)
    (left right : T),
    Box.Insts.CoreCmpPartialEqBox.ne A inst left right = inst.ne left right
  boxAsRef : forall {T : Type} (A : Type) (value : T),
    Box.Insts.CoreConvertAsRef.as_ref A value = .ok value
  btreeNew : forall (T : Type),
    alloc.collections.btree.set.BTreeSetTGlobal.new T = .ok []
  btreeInsert : forall {T A : Type} (cloneAllocator : core.clone.Clone A)
    (ord : core.cmp.Ord T) (values : alloc.collections.btree.set.BTreeSet T A)
    (value : T) (present : Bool),
    List.anyM (fun existing => ord.eqInst.partialEqInst.eq existing value) values =
      .ok present ->
    alloc.collections.btree.set.BTreeSet.insert cloneAllocator ord values value =
      .ok (!present, if present then values else value :: values)
  strToOwned : forall value : Str, exists owned,
    Str.Insts.AllocBorrowToOwnedString.to_owned value = .ok owned
  stringEq : forall left right : String,
    alloc.string.String.Insts.CoreCmpPartialEqString.eq left right =
      .ok (left == right)
  stringPartialCmp : forall left right : String,
    alloc.string.String.Insts.CoreCmpPartialOrdString.partial_cmp left right =
      .ok (some (compare left right))
  stringCmp : forall left right : String,
    alloc.string.String.Insts.CoreCmpOrd.cmp left right = .ok (compare left right)
  stringIsEmpty : forall value : String,
    alloc.string.String.is_empty value = .ok value.isEmpty
  stringClone : forall value : String,
    alloc.string.String.Insts.CoreCloneClone.clone value = .ok value
  sliceNextWithin : forall {T : Type} (iter : core.slice.iter.Iter T),
    iter.i < iter.slice.len -> exists value next,
      core.slice.iter.IteratorSliceIter.next iter = .ok (some value, next) /\
      next.slice = iter.slice /\ next.i = iter.i + 1
  sliceNextExhausted : forall {T : Type} (iter : core.slice.iter.Iter T),
    (¬ iter.i < iter.slice.len) ->
      core.slice.iter.IteratorSliceIter.next iter = .ok (none, iter)
  vec : ModelVecRefinement

theorem reachable_standard_library_refinement :
    ReachableStandardLibraryRefinement := {
  mustUse := must_use_refines
  sharedGt := shared_gt_refines
  optionSome := option_ok_or_else_some_refines
  optionNone := option_ok_or_else_none_refines
  cloneNone := option_cloned_none_refines
  cloneSome := option_cloned_some_refines
  boxNe := box_ne_refines
  boxAsRef := box_as_ref_refines
  btreeNew := btree_set_new_refines
  btreeInsert := btree_set_insert_refines
  strToOwned := str_to_owned_total
  stringEq := string_eq_refines
  stringPartialCmp := string_partial_cmp_refines
  stringCmp := string_cmp_refines
  stringIsEmpty := string_is_empty_refines
  stringClone := string_clone_refines
  sliceNextWithin := slice_iterator_next_within_refines
  sliceNextExhausted := slice_iterator_next_exhausted_refines
  vec := recursive_vec_list_refinement
}

end VcTermSort.Proofs
