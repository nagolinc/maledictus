import TypeAlgebraKernelProofs.AssignabilityExact

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace TypeAlgebraKernel.Proofs

open TypeAlgebraKernel
open python_type_algebra_kernel

theorem flattenUnionReference_bounded
    (types flattened : PyTypeList)
    (typesBounded : boundedTypeList types)
    (flattenedBounded : boundedTypeList flattened) :
    boundedTypeList (flattenUnionReference types flattened) := by
  rw [flattenUnionReference.eq_def]
  cases types with
  | Empty => exact flattenedBounded
  | Item ty tail =>
      have tyBounded : boundedType ty := typesBounded.1
      have tailBounded : boundedTypeList tail := typesBounded.2
      cases ty
      case Union nested =>
        simp only
        apply flattenUnionReference_bounded tail _ tailBounded
        exact flattenUnionReference_bounded nested flattened tyBounded flattenedBounded
      all_goals
        simp only
        split
        · exact flattenUnionReference_bounded tail flattened tailBounded flattenedBounded
        · apply flattenUnionReference_bounded tail _ tailBounded
          exact And.intro tyBounded flattenedBounded
termination_by typeListSize types
decreasing_by
  all_goals simp_all [typeSize, typeListSize]
  all_goals omega

theorem reverseTypeListReference_bounded
    (types reversed : PyTypeList)
    (typesBounded : boundedTypeList types)
    (reversedBounded : boundedTypeList reversed) :
    boundedTypeList (reverseTypeListReference types reversed) := by
  rw [reverseTypeListReference.eq_def]
  cases types with
  | Empty => exact reversedBounded
  | Item ty tail =>
      exact reverseTypeListReference_bounded tail (.Item ty reversed) typesBounded.2
        (And.intro typesBounded.1 reversedBounded)
termination_by typeListSize types
decreasing_by simp_all [typeListSize]

theorem normalizeTypeListReference_bounded
    (types : PyTypeList)
    (typesBounded : boundedTypeList types) :
    boundedType (normalizeTypeListReference types) := by
  have flattenedBounded :
      boundedTypeList (flattenUnionReference types .Empty) :=
    flattenUnionReference_bounded types .Empty typesBounded True.intro
  have reversedBounded :
      boundedTypeList
        (reverseTypeListReference (flattenUnionReference types .Empty) .Empty) :=
    reverseTypeListReference_bounded (flattenUnionReference types .Empty) .Empty
      flattenedBounded True.intro
  change boundedType
    (match reverseTypeListReference (flattenUnionReference types .Empty) .Empty with
    | .Item single .Empty => single
    | other => .Union other)
  cases reversed : reverseTypeListReference (flattenUnionReference types .Empty) .Empty with
  | Empty =>
      rw [reversed] at reversedBounded
      exact True.intro
  | Item single tail =>
      rw [reversed] at reversedBounded
      cases tail with
      | Empty =>
          simpa [reversed, boundedType, boundedTypeList] using reversedBounded.1
      | Item next rest =>
          change boundedTypeList (.Item single (.Item next rest))
          exact reversedBounded

theorem expandUnionListReference_bounded
    (ty : PyType)
    (tyBounded : boundedType ty) :
    boundedTypeList (expandUnionListReference ty) := by
  have normalizedBounded : boundedType (normalizeTypeListReference (.Item ty .Empty)) :=
    normalizeTypeListReference_bounded (.Item ty .Empty) (And.intro tyBounded True.intro)
  change boundedTypeList
    (match normalizeTypeListReference (.Item ty .Empty) with
    | .Union types => types
    | other => .Item other .Empty)
  cases normalized : normalizeTypeListReference (.Item ty .Empty) with
  | Union types =>
      rw [normalized] at normalizedBounded
      change boundedTypeList types at normalizedBounded
      exact normalizedBounded
  | Int | Bool | Str | None | Object | Class | List | Set | Dict | FixedTuple | VariadicTuple =>
      rw [normalized] at normalizedBounded
      exact And.intro normalizedBounded True.intro

def narrowVariantsAllReference
    (variants : PyTypeList)
    (expected : PyType)
    (positive : Bool)
    (hierarchy : NominalHierarchy) : Result PyTypeList :=
  match variants with
  | .Empty => .ok .Empty
  | .Item variant tail => do
      let retainedTail <- narrowVariantsAllReference tail expected positive hierarchy
      let inside <- assignableAllReference variant expected hierarchy
      let containsExpected <- assignableAllReference expected variant hierarchy
      if positive then
        if inside then .ok (.Item variant retainedTail)
        else if containsExpected then .ok (.Item expected retainedTail)
        else .ok retainedTail
      else if inside then
        .ok retainedTail
      else
        .ok (.Item variant retainedTail)

theorem narrow_variants_all_inputs_exact
    (variants : PyTypeList)
    (expected : PyType)
    (positive : Bool)
    (hierarchy : NominalHierarchy) :
    narrow_variants variants expected positive hierarchy =
      narrowVariantsAllReference variants expected positive hierarchy := by
  rw [narrow_variants.eq_def]
  cases variants with
  | Empty =>
      rw [narrowVariantsAllReference.eq_def]
  | Item variant tail =>
      rw [narrowVariantsAllReference.eq_def]
      simp only
      rw [narrow_variants_all_inputs_exact tail expected positive hierarchy]
      cases tailResult : narrowVariantsAllReference tail expected positive hierarchy with
      | fail error => rfl
      | div => rfl
      | ok retainedTail =>
          rw [is_assignable_all_inputs_exact variant expected hierarchy]
          cases insideResult : assignableAllReference variant expected hierarchy with
          | fail error => rfl
          | div => rfl
          | ok inside =>
              rw [is_assignable_all_inputs_exact expected variant hierarchy]
              cases containsResult : assignableAllReference expected variant hierarchy with
              | fail error => rfl
              | div => rfl
              | ok containsExpected =>
                  cases positive <;> cases inside <;> cases containsExpected <;>
                    simp [clone_type_exact]
termination_by typeListSize variants
decreasing_by simp_all [typeListSize]

def narrowVariantsReference
    (variants : PyTypeList)
    (expected : PyType)
    (positive : Bool)
    (hierarchy : NominalHierarchy)
    (variantsBounded : boundedTypeList variants)
    (expectedBounded : boundedType expected)
    (classesBounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize) : PyTypeList :=
  match variants with
  | .Empty => .Empty
  | .Item variant tail =>
      let retainedTail := narrowVariantsReference tail expected positive hierarchy
        variantsBounded.2 expectedBounded classesBounded remaining
      let inside := assignableReference variant expected hierarchy variantsBounded.1
        expectedBounded classesBounded remaining
      let containsExpected := assignableReference expected variant hierarchy expectedBounded
        variantsBounded.1 classesBounded remaining
      if positive && inside then .Item variant retainedTail
      else if positive && containsExpected then .Item expected retainedTail
      else if !positive && !inside then .Item variant retainedTail
      else retainedTail

theorem narrow_variants_exact
    (variants : PyTypeList)
    (expected : PyType)
    (positive : Bool)
    (hierarchy : NominalHierarchy)
    (variantsBounded : boundedTypeList variants)
    (expectedBounded : boundedType expected)
    (classesBounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize)
    (lengthExact : NominalClassList.len hierarchy.classes = .ok remaining) :
    narrow_variants variants expected positive hierarchy =
      .ok (narrowVariantsReference variants expected positive hierarchy variantsBounded
        expectedBounded classesBounded remaining) := by
  rw [narrow_variants.eq_def]
  cases variants with
  | Empty => rfl
  | Item variant tail =>
      have variantBounded : boundedType variant := variantsBounded.1
      have tailBounded : boundedTypeList tail := variantsBounded.2
      simp only [narrowVariantsReference]
      rw [narrow_variants_exact tail expected positive hierarchy tailBounded expectedBounded
        classesBounded remaining lengthExact]
      simp only [bind_tc_ok]
      rw [is_assignable_exact variant expected hierarchy variantBounded expectedBounded
        classesBounded remaining lengthExact]
      simp only [bind_tc_ok]
      rw [is_assignable_exact expected variant hierarchy expectedBounded variantBounded
        classesBounded remaining lengthExact]
      simp only [bind_tc_ok]
      cases positive <;>
        cases assignableReference variant expected hierarchy variantBounded expectedBounded
          classesBounded remaining <;>
        cases assignableReference expected variant hierarchy expectedBounded variantBounded
          classesBounded remaining <;>
        simp [clone_type_exact]
termination_by typeListSize variants
decreasing_by simp_all [typeListSize]

def narrowTypeReference
    (actual expected : PyType)
    (positive : Bool)
    (hierarchy : NominalHierarchy)
    (actualBounded : boundedType actual)
    (expectedBounded : boundedType expected)
    (variantsBounded : boundedTypeList (expandUnionListReference actual))
    (classesBounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize) : Option PyType :=
  if typeWellFormedReference actual hierarchy actualBounded classesBounded then
    if typeWellFormedReference expected hierarchy expectedBounded classesBounded then
      let retained := narrowVariantsReference (expandUnionListReference actual) expected positive
        hierarchy variantsBounded expectedBounded classesBounded remaining
      match retained with
      | .Empty => none
      | .Item _ _ => some (normalizeTypeListReference retained)
    else none
  else none

/-- Exact narrowing refinement with the normalized-list representation witness
    made explicit for reuse by the closed public theorem below. -/
theorem narrow_type_with_variants_exact
    (actual expected : PyType)
    (positive : Bool)
    (hierarchy : NominalHierarchy)
    (actualBounded : boundedType actual)
    (expectedBounded : boundedType expected)
    (variantsBounded : boundedTypeList (expandUnionListReference actual))
    (classesBounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize)
    (lengthExact : NominalClassList.len hierarchy.classes = .ok remaining) :
    narrow_type actual expected positive hierarchy =
      .ok (narrowTypeReference actual expected positive hierarchy actualBounded expectedBounded
        variantsBounded classesBounded remaining) := by
  unfold narrow_type narrowTypeReference
  rw [type_is_well_formed_exact actual hierarchy actualBounded classesBounded]
  cases actualFormed : typeWellFormedReference actual hierarchy actualBounded classesBounded
  · rfl
  · rw [type_is_well_formed_exact expected hierarchy expectedBounded classesBounded]
    cases expectedFormed : typeWellFormedReference expected hierarchy expectedBounded classesBounded
    · rfl
    · rw [expand_union_list_exact]
      simp only [bind_tc_ok]
      rw [narrow_variants_exact (expandUnionListReference actual) expected positive hierarchy
        variantsBounded expectedBounded classesBounded remaining lengthExact]
      simp only [bind_tc_ok]
      cases retained : narrowVariantsReference (expandUnionListReference actual) expected positive
          hierarchy variantsBounded expectedBounded classesBounded remaining with
      | Empty => rfl
      | Item head tail =>
          rw [normalize_type_list_exact]
          simp

/-- Universal exact refinement of production narrowing. The normalized-list
    representation premise is derived from the bounded ingress type. -/
theorem narrow_type_exact
    (actual expected : PyType)
    (positive : Bool)
    (hierarchy : NominalHierarchy)
    (actualBounded : boundedType actual)
    (expectedBounded : boundedType expected)
    (classesBounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize)
    (lengthExact : NominalClassList.len hierarchy.classes = .ok remaining) :
    narrow_type actual expected positive hierarchy =
      .ok (narrowTypeReference actual expected positive hierarchy actualBounded expectedBounded
        (expandUnionListReference_bounded actual actualBounded) classesBounded remaining) := by
  exact narrow_type_with_variants_exact actual expected positive hierarchy actualBounded
    expectedBounded (expandUnionListReference_bounded actual actualBounded) classesBounded
    remaining lengthExact

end TypeAlgebraKernel.Proofs
