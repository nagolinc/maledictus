import VcTermSortProofs.DerivedTraits

namespace VcTermSort.Proofs

def TermStrictlySmaller (child parent : VcTermSort.Term) : Prop :=
  sizeOf child < sizeOf parent

theorem term_strictly_smaller_well_founded :
    WellFounded TermStrictlySmaller := by
  exact WellFounded.onFun (f := sizeOf) Nat.lt_wfRel.wf

theorem immediate_child_strictly_smaller
    (child parent : VcTermSort.Term)
    (shape : sizeOf parent = sizeOf child + 1) :
    TermStrictlySmaller child parent := by
  unfold TermStrictlySmaller
  omega

theorem first_binary_child_strictly_smaller
    (left right parent : VcTermSort.Term)
    (shape : sizeOf parent = 1 + sizeOf left + sizeOf right) :
    TermStrictlySmaller left parent := by
  unfold TermStrictlySmaller
  omega

theorem second_binary_child_strictly_smaller
    (left right parent : VcTermSort.Term)
    (shape : sizeOf parent = 1 + sizeOf left + sizeOf right) :
    TermStrictlySmaller right parent := by
  unfold TermStrictlySmaller
  omega

theorem list_member_strictly_smaller
    (child : VcTermSort.Term) (children : List VcTermSort.Term)
    (parent : VcTermSort.Term) (member : child ∈ children)
    (shape : sizeOf parent = sizeOf children + 1) :
    TermStrictlySmaller child parent := by
  unfold TermStrictlySmaller
  have child_below_list : sizeOf child < sizeOf children :=
    List.sizeOf_lt_of_mem member
  omega

theorem optional_child_strictly_smaller
    (child : VcTermSort.Term) (optional : Option VcTermSort.Term)
    (parent : VcTermSort.Term) (present : optional = some child)
    (shape : sizeOf parent >= sizeOf optional + 1) :
    TermStrictlySmaller child parent := by
  subst optional
  unfold TermStrictlySmaller
  simp at shape
  omega

theorem permission_receiver_strictly_smaller
    (amount : VcTermSort.PermissionTransferAmount)
    (amounts : List VcTermSort.PermissionTransferAmount)
    (parent : VcTermSort.Term) (member : amount ∈ amounts)
    (shape : sizeOf parent >= sizeOf amounts + 1) :
    TermStrictlySmaller amount.receiver parent := by
  cases amount with
  | mk receiver numerator denominator =>
      unfold TermStrictlySmaller
      have amount_below_list :
          sizeOf (VcTermSort.PermissionTransferAmount.mk receiver numerator denominator) <
            sizeOf amounts := List.sizeOf_lt_of_mem member
      simp at amount_below_list ⊢
      omega

theorem finite_dict_key_strictly_smaller
    (entry : VcTermSort.Term × VcTermSort.Term)
    (entries : List (VcTermSort.Term × VcTermSort.Term))
    (parent : VcTermSort.Term) (member : entry ∈ entries)
    (shape : sizeOf parent >= sizeOf entries + 1) :
    TermStrictlySmaller entry.1 parent := by
  rcases entry with ⟨key, value⟩
  unfold TermStrictlySmaller
  have entry_below_list : sizeOf (key, value) < sizeOf entries :=
    List.sizeOf_lt_of_mem member
  simp at entry_below_list ⊢
  omega

theorem finite_dict_value_strictly_smaller
    (entry : VcTermSort.Term × VcTermSort.Term)
    (entries : List (VcTermSort.Term × VcTermSort.Term))
    (parent : VcTermSort.Term) (member : entry ∈ entries)
    (shape : sizeOf parent >= sizeOf entries + 1) :
    TermStrictlySmaller entry.2 parent := by
  rcases entry with ⟨key, value⟩
  unfold TermStrictlySmaller
  have entry_below_list : sizeOf (key, value) < sizeOf entries :=
    List.sizeOf_lt_of_mem member
  simp at entry_below_list ⊢
  omega

/-- The complete nested storage forms through which the production recursive
    helpers can reach another `Term`. This is the well-founded measure input to
    the mutual no-divergence proof; it does not itself claim that every
    generated call site has already been connected to the relation. -/
structure RecursiveStorageMeasure : Prop where
  wellFounded : WellFounded TermStrictlySmaller
  immediate : ∀ (child parent : VcTermSort.Term),
    sizeOf parent = sizeOf child + 1 → TermStrictlySmaller child parent
  firstBinary : ∀ (left right parent : VcTermSort.Term),
    sizeOf parent = 1 + sizeOf left + sizeOf right →
      TermStrictlySmaller left parent
  secondBinary : ∀ (left right parent : VcTermSort.Term),
    sizeOf parent = 1 + sizeOf left + sizeOf right →
      TermStrictlySmaller right parent
  listMember : ∀ (child : VcTermSort.Term) (children : List VcTermSort.Term)
    (parent : VcTermSort.Term), child ∈ children →
    sizeOf parent = sizeOf children + 1 → TermStrictlySmaller child parent
  optional : ∀ (child : VcTermSort.Term) (optional : Option VcTermSort.Term)
    (parent : VcTermSort.Term), optional = some child →
    sizeOf parent ≥ sizeOf optional + 1 → TermStrictlySmaller child parent
  permissionReceiver : ∀ (amount : VcTermSort.PermissionTransferAmount)
    (amounts : List VcTermSort.PermissionTransferAmount)
    (parent : VcTermSort.Term), amount ∈ amounts →
    sizeOf parent ≥ sizeOf amounts + 1 →
      TermStrictlySmaller amount.receiver parent
  finiteDictKey : ∀ (entry : VcTermSort.Term × VcTermSort.Term)
    (entries : List (VcTermSort.Term × VcTermSort.Term))
    (parent : VcTermSort.Term), entry ∈ entries →
    sizeOf parent ≥ sizeOf entries + 1 → TermStrictlySmaller entry.1 parent
  finiteDictValue : ∀ (entry : VcTermSort.Term × VcTermSort.Term)
    (entries : List (VcTermSort.Term × VcTermSort.Term))
    (parent : VcTermSort.Term), entry ∈ entries →
    sizeOf parent ≥ sizeOf entries + 1 → TermStrictlySmaller entry.2 parent

theorem recursive_storage_measure : RecursiveStorageMeasure := {
  wellFounded := term_strictly_smaller_well_founded
  immediate := immediate_child_strictly_smaller
  firstBinary := first_binary_child_strictly_smaller
  secondBinary := second_binary_child_strictly_smaller
  listMember := list_member_strictly_smaller
  optional := optional_child_strictly_smaller
  permissionReceiver := permission_receiver_strictly_smaller
  finiteDictKey := finite_dict_key_strictly_smaller
  finiteDictValue := finite_dict_value_strictly_smaller
}

end VcTermSort.Proofs
