import TypeAlgebraKernelProofs.Assignability

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace TypeAlgebraKernel.Proofs

open TypeAlgebraKernel
open python_type_algebra_kernel

def nominalAssignableAllReference
    (actual expected : String)
    (hierarchy : NominalHierarchy) : Result Bool :=
  if actualBounded : actual.toByteArray.size <= U32.max then
    if expectedBounded : expected.toByteArray.size <= U32.max then
      isSubclassAllReference (toStr actual actualBounded) (toStr expected expectedBounded) hierarchy
    else
      .fail .panic
  else
    .fail .panic

mutual
  def assignableValidAllReference
      (actual expected : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy) : Result Bool :=
    if typeEqReference actual expected then .ok true
    else if (match expected with | .Object => true | _ => false) then .ok true
    else
      match actual, expected with
      | .Bool, .Int => .ok true
      | .Class actualName, .Class expectedName =>
          nominalAssignableAllReference actualName expectedName hierarchy
      | .Union actualTypes, expectedType =>
          everyAssignableAllReference actualTypes expectedType hierarchy
      | actualType, .Union expectedTypes =>
          anyAssignableAllReference actualType expectedTypes hierarchy
      | .FixedTuple actualTypes, .FixedTuple expectedTypes =>
          listsAssignableAllReference actualTypes expectedTypes hierarchy
      | .FixedTuple actualTypes, .VariadicTuple expectedType =>
          everyAssignableAllReference actualTypes expectedType hierarchy
      | .VariadicTuple actualType, .VariadicTuple expectedType =>
          assignableValidAllReference actualType expectedType hierarchy
      | _, _ => .ok false
  termination_by typeSize actual + typeSize expected

  def everyAssignableAllReference
      (actual : python_type_algebra_kernel.TypeList)
      (expected : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy) : Result Bool :=
    match actual with
    | .Empty => .ok true
    | .Item head tail => do
        let headAssignable <- assignableValidAllReference head expected hierarchy
        if headAssignable then everyAssignableAllReference tail expected hierarchy else .ok false
  termination_by typeListSize actual + typeSize expected

  def anyAssignableAllReference
      (actual : python_type_algebra_kernel.Type)
      (expected : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy) : Result Bool :=
    match expected with
    | .Empty => .ok false
    | .Item head tail => do
        let headAssignable <- assignableValidAllReference actual head hierarchy
        if headAssignable then .ok true else anyAssignableAllReference actual tail hierarchy
  termination_by typeSize actual + typeListSize expected

  def listsAssignableAllReference
      (actual expected : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy) : Result Bool :=
    match actual, expected with
    | .Empty, .Empty => .ok true
    | .Item actualHead actualTail, .Item expectedHead expectedTail => do
        let headsAssignable <-
          assignableValidAllReference actualHead expectedHead hierarchy
        if headsAssignable then
          listsAssignableAllReference actualTail expectedTail hierarchy
        else
          .ok false
    | _, _ => .ok false
  termination_by typeListSize actual + typeListSize expected
  decreasing_by
    all_goals simp [typeListSize]
    all_goals omega
end

mutual
  theorem is_assignable_in_valid_hierarchy_all_inputs_exact
      (actual expected : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy) :
      is_assignable_in_valid_hierarchy actual expected hierarchy =
        assignableValidAllReference actual expected hierarchy := by
    rw [is_assignable_in_valid_hierarchy.eq_def, type_equals_exact]
    by_cases sameType : typeEqReference actual expected
    · rw [assignableValidAllReference.eq_def]
      simp [sameType]
    · simp only [sameType, Bool.false_eq_true, if_false, bind_tc_ok]
      rw [assignableValidAllReference.eq_def]
      simp only [sameType, Bool.false_eq_true, if_false]
      cases actual <;> cases expected <;>
        simp_all only [typeEqReference, bind_tc_ok, if_false, if_true,
          Bool.false_eq_true]
      all_goals try contradiction
      all_goals try rw [type_assignable_to_any_all_inputs_exact _ _ hierarchy]
      all_goals try rw [every_type_assignable_to_all_inputs_exact _ _ hierarchy]
      all_goals try rw [type_lists_assignable_all_inputs_exact _ _ hierarchy]
      all_goals try rw [is_assignable_in_valid_hierarchy_all_inputs_exact _ _ hierarchy]
      case neg.Class.Class actualName expectedName =>
        unfold alloc.string.String.Insts.CoreOpsDerefDerefStr.deref
        unfold nominalAssignableAllReference
        by_cases actualBounded : actualName.toByteArray.size <= U32.max
        · by_cases expectedBounded : expectedName.toByteArray.size <= U32.max
          · simp only [dif_pos actualBounded, dif_pos expectedBounded, bind_tc_ok]
            rw [is_subclass_all_inputs_exact]
          · simp only [dif_pos actualBounded, dif_neg expectedBounded,
              bind_tc_ok, bind_tc_fail]
        · simp only [dif_neg actualBounded, bind_tc_fail]
  termination_by typeSize actual + typeSize expected

  theorem every_type_assignable_to_all_inputs_exact
      (actual : python_type_algebra_kernel.TypeList)
      (expected : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy) :
      every_type_assignable_to actual expected hierarchy =
        everyAssignableAllReference actual expected hierarchy := by
    rw [every_type_assignable_to.eq_def]
    cases actual with
    | Empty =>
        rw [everyAssignableAllReference.eq_def]
    | Item head tail =>
        rw [everyAssignableAllReference.eq_def]
        simp only
        change (do
          let headAssignable <- is_assignable_in_valid_hierarchy head expected hierarchy
          if headAssignable then every_type_assignable_to tail expected hierarchy
          else .ok false) = _
        rw [is_assignable_in_valid_hierarchy_all_inputs_exact]
        cases headResult : assignableValidAllReference head expected hierarchy with
        | fail error => rfl
        | div => rfl
        | ok headAssignable =>
            cases headAssignable
            · rfl
            · exact every_type_assignable_to_all_inputs_exact tail expected hierarchy
  termination_by typeListSize actual + typeSize expected

  theorem type_assignable_to_any_all_inputs_exact
      (actual : python_type_algebra_kernel.Type)
      (expected : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy) :
      type_assignable_to_any actual expected hierarchy =
        anyAssignableAllReference actual expected hierarchy := by
    rw [type_assignable_to_any.eq_def]
    cases expected with
    | Empty =>
        rw [anyAssignableAllReference.eq_def]
    | Item head tail =>
        rw [anyAssignableAllReference.eq_def]
        simp only
        change (do
          let headAssignable <- is_assignable_in_valid_hierarchy actual head hierarchy
          if headAssignable then .ok true
          else type_assignable_to_any actual tail hierarchy) = _
        rw [is_assignable_in_valid_hierarchy_all_inputs_exact]
        cases headResult : assignableValidAllReference actual head hierarchy with
        | fail error => rfl
        | div => rfl
        | ok headAssignable =>
            cases headAssignable
            · exact type_assignable_to_any_all_inputs_exact actual tail hierarchy
            · rfl
  termination_by typeSize actual + typeListSize expected

  theorem type_lists_assignable_all_inputs_exact
      (actual expected : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy) :
      type_lists_assignable actual expected hierarchy =
        listsAssignableAllReference actual expected hierarchy := by
    rw [type_lists_assignable.eq_def]
    cases actual with
    | Empty =>
        cases expected <;> rw [listsAssignableAllReference.eq_def]
    | Item actualHead actualTail =>
        cases expected with
        | Empty => rw [listsAssignableAllReference.eq_def]
        | Item expectedHead expectedTail =>
            rw [listsAssignableAllReference.eq_def]
            simp only
            change (do
              let headsAssignable <-
                is_assignable_in_valid_hierarchy actualHead expectedHead hierarchy
              if headsAssignable then
                type_lists_assignable actualTail expectedTail hierarchy
              else .ok false) = _
            rw [is_assignable_in_valid_hierarchy_all_inputs_exact]
            cases headResult :
                assignableValidAllReference actualHead expectedHead hierarchy with
            | fail error => rfl
            | div => rfl
            | ok headsAssignable =>
                cases headsAssignable
                · rfl
                · exact type_lists_assignable_all_inputs_exact actualTail expectedTail hierarchy
  termination_by typeListSize actual + typeListSize expected
end

def assignableAllReference
    (actual expected : python_type_algebra_kernel.Type)
    (hierarchy : NominalHierarchy) : Result Bool := do
  let actualFormed <- typeWellFormedAllReference actual hierarchy
  if actualFormed then
    let expectedFormed <- typeWellFormedAllReference expected hierarchy
    if expectedFormed then assignableValidAllReference actual expected hierarchy else .ok false
  else
    .ok false

theorem is_assignable_all_inputs_exact
    (actual expected : python_type_algebra_kernel.Type)
    (hierarchy : NominalHierarchy) :
    is_assignable actual expected hierarchy =
      assignableAllReference actual expected hierarchy := by
  unfold is_assignable assignableAllReference
  rw [type_is_well_formed_all_inputs_exact]
  cases actualResult : typeWellFormedAllReference actual hierarchy with
  | fail error => rfl
  | div => rfl
  | ok actualFormed =>
      cases actualFormed
      · rfl
      · rw [type_is_well_formed_all_inputs_exact]
        cases expectedResult : typeWellFormedAllReference expected hierarchy with
        | fail error => rfl
        | div => rfl
        | ok expectedFormed =>
            cases expectedFormed
            · rfl
            · exact is_assignable_in_valid_hierarchy_all_inputs_exact actual expected hierarchy

mutual
  theorem is_assignable_in_valid_hierarchy_exact
      (actual expected : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy)
      (actualBounded : boundedType actual)
      (expectedBounded : boundedType expected)
      (classesBounded : boundedNominalClasses hierarchy.classes)
      (remaining : Usize)
      (lengthExact : NominalClassList.len hierarchy.classes = .ok remaining) :
      is_assignable_in_valid_hierarchy actual expected hierarchy =
        .ok (assignableValidReference actual expected hierarchy classesBounded remaining) := by
    rw [is_assignable_in_valid_hierarchy.eq_def, type_equals_exact]
    by_cases sameType : typeEqReference actual expected
    · rw [assignableValidReference.eq_def]
      simp [sameType]
    · simp only [sameType, Bool.false_eq_true, if_false, bind_tc_ok]
      rw [assignableValidReference.eq_def]
      simp only [sameType, Bool.false_eq_true, if_false]
      cases actual <;> cases expected <;>
        simp_all only [typeEqReference, bind_tc_ok, if_false, if_true,
          Bool.false_eq_true]
      all_goals try rw [type_assignable_to_any_exact _ _ hierarchy (by assumption)
        (by assumption) classesBounded remaining lengthExact]
      all_goals try rw [every_type_assignable_to_exact _ _ hierarchy (by assumption)
        (by assumption) classesBounded remaining lengthExact]
      all_goals try rw [type_lists_assignable_exact _ _ hierarchy (by assumption)
        (by assumption) classesBounded remaining lengthExact]
      all_goals try rw [is_assignable_in_valid_hierarchy_exact _ _ hierarchy (by assumption)
        (by assumption) classesBounded remaining lengthExact]
      case neg.Class.Class actualName expectedName =>
        have actualNameBounded : actualName.toByteArray.size <= U32.max := actualBounded
        have expectedNameBounded : expectedName.toByteArray.size <= U32.max := expectedBounded
        unfold alloc.string.String.Insts.CoreOpsDerefDerefStr.deref
        rw [dif_pos actualNameBounded, dif_pos expectedNameBounded]
        simp only [bind_tc_ok]
        rw [is_subclass_exact (toStr actualName actualNameBounded)
          (toStr expectedName expectedNameBounded) hierarchy classesBounded remaining lengthExact]
        unfold nominalAssignableReference
        rw [dif_pos actualNameBounded, dif_pos expectedNameBounded]
  termination_by typeSize actual + typeSize expected

  theorem every_type_assignable_to_exact
      (actual : python_type_algebra_kernel.TypeList)
      (expected : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy)
      (actualBounded : boundedTypeList actual)
      (expectedBounded : boundedType expected)
      (classesBounded : boundedNominalClasses hierarchy.classes)
      (remaining : Usize)
      (lengthExact : NominalClassList.len hierarchy.classes = .ok remaining) :
      every_type_assignable_to actual expected hierarchy =
        .ok (everyAssignableReference actual expected hierarchy classesBounded remaining) := by
    rw [every_type_assignable_to.eq_def]
    cases actual with
    | Empty => simp [everyAssignableReference.eq_def]
    | Item head tail =>
        have headBounded : boundedType head := actualBounded.1
        have tailBounded : boundedTypeList tail := actualBounded.2
        simp only [everyAssignableReference]
        rw [is_assignable_in_valid_hierarchy_exact head expected hierarchy headBounded
          expectedBounded classesBounded remaining lengthExact]
        cases assignableValidReference head expected hierarchy classesBounded remaining
        · rfl
        · rw [every_type_assignable_to_exact tail expected hierarchy tailBounded
              expectedBounded classesBounded remaining lengthExact]
          simp
  termination_by typeListSize actual + typeSize expected

  theorem type_assignable_to_any_exact
      (actual : python_type_algebra_kernel.Type)
      (expected : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy)
      (actualBounded : boundedType actual)
      (expectedBounded : boundedTypeList expected)
      (classesBounded : boundedNominalClasses hierarchy.classes)
      (remaining : Usize)
      (lengthExact : NominalClassList.len hierarchy.classes = .ok remaining) :
      type_assignable_to_any actual expected hierarchy =
        .ok (anyAssignableReference actual expected hierarchy classesBounded remaining) := by
    rw [type_assignable_to_any.eq_def]
    cases expected with
    | Empty => simp [anyAssignableReference.eq_def]
    | Item head tail =>
        have headBounded : boundedType head := expectedBounded.1
        have tailBounded : boundedTypeList tail := expectedBounded.2
        simp only [anyAssignableReference]
        rw [is_assignable_in_valid_hierarchy_exact actual head hierarchy actualBounded
          headBounded classesBounded remaining lengthExact]
        cases assignableValidReference actual head hierarchy classesBounded remaining
        · rw [type_assignable_to_any_exact actual tail hierarchy actualBounded tailBounded
              classesBounded remaining lengthExact]
          rfl
        · rfl
  termination_by typeSize actual + typeListSize expected

  theorem type_lists_assignable_exact
      (actual expected : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy)
      (actualBounded : boundedTypeList actual)
      (expectedBounded : boundedTypeList expected)
      (classesBounded : boundedNominalClasses hierarchy.classes)
      (remaining : Usize)
      (lengthExact : NominalClassList.len hierarchy.classes = .ok remaining) :
      type_lists_assignable actual expected hierarchy =
        .ok (listsAssignableReference actual expected hierarchy classesBounded remaining) := by
    rw [type_lists_assignable.eq_def]
    cases actual <;> cases expected <;> simp only [listsAssignableReference]
    case Item.Item actualHead actualTail expectedHead expectedTail =>
      have actualHeadBounded : boundedType actualHead := actualBounded.1
      have actualTailBounded : boundedTypeList actualTail := actualBounded.2
      have expectedHeadBounded : boundedType expectedHead := expectedBounded.1
      have expectedTailBounded : boundedTypeList expectedTail := expectedBounded.2
      rw [is_assignable_in_valid_hierarchy_exact actualHead expectedHead hierarchy
        actualHeadBounded expectedHeadBounded classesBounded remaining lengthExact]
      cases assignableValidReference actualHead expectedHead hierarchy classesBounded remaining
      · rfl
      · rw [type_lists_assignable_exact actualTail expectedTail hierarchy actualTailBounded
            expectedTailBounded classesBounded remaining lengthExact]
        simp
  termination_by typeListSize actual + typeListSize expected
end

def assignableReference
    (actual expected : python_type_algebra_kernel.Type)
    (hierarchy : NominalHierarchy)
    (actualBounded : boundedType actual)
    (expectedBounded : boundedType expected)
    (classesBounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize) : Bool :=
  typeWellFormedReference actual hierarchy actualBounded classesBounded &&
    typeWellFormedReference expected hierarchy expectedBounded classesBounded &&
      assignableValidReference actual expected hierarchy classesBounded remaining

/-- Universal exact refinement of the production assignability decision over
    every source-representable type and validated nominal hierarchy. -/
theorem is_assignable_exact
    (actual expected : python_type_algebra_kernel.Type)
    (hierarchy : NominalHierarchy)
    (actualBounded : boundedType actual)
    (expectedBounded : boundedType expected)
    (classesBounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize)
    (lengthExact : NominalClassList.len hierarchy.classes = .ok remaining) :
    is_assignable actual expected hierarchy =
      .ok (assignableReference actual expected hierarchy actualBounded expectedBounded
        classesBounded remaining) := by
  unfold is_assignable assignableReference
  rw [type_is_well_formed_exact actual hierarchy actualBounded classesBounded]
  cases typeWellFormedReference actual hierarchy actualBounded classesBounded
  · rfl
  · rw [type_is_well_formed_exact expected hierarchy expectedBounded classesBounded]
    cases typeWellFormedReference expected hierarchy expectedBounded classesBounded
    · rfl
    · rw [is_assignable_in_valid_hierarchy_exact actual expected hierarchy actualBounded
          expectedBounded classesBounded remaining lengthExact]
      rfl

def castCompatibleReference
    (actual expected : python_type_algebra_kernel.Type)
    (hierarchy : NominalHierarchy)
    (actualBounded : boundedType actual)
    (expectedBounded : boundedType expected)
    (classesBounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize) : Bool :=
  if typeWellFormedReference actual hierarchy actualBounded classesBounded then
    if typeWellFormedReference expected hierarchy expectedBounded classesBounded then
      match expected with
      | .VariadicTuple element =>
          if typeEqReference element .Object then
            match actual with
            | .FixedTuple _ | .VariadicTuple _ => true
            | _ => false
          else
            assignableValidReference actual expected hierarchy classesBounded remaining
      | _ =>
          assignableValidReference actual expected hierarchy classesBounded remaining
    else false
  else false

/-- Universal exact refinement of the production cast-compatibility decision. -/
theorem cast_compatible_exact
    (actual expected : python_type_algebra_kernel.Type)
    (hierarchy : NominalHierarchy)
    (actualBounded : boundedType actual)
    (expectedBounded : boundedType expected)
    (classesBounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize)
    (lengthExact : NominalClassList.len hierarchy.classes = .ok remaining) :
    cast_compatible actual expected hierarchy =
      .ok (castCompatibleReference actual expected hierarchy actualBounded expectedBounded
        classesBounded remaining) := by
  unfold cast_compatible castCompatibleReference
  rw [type_is_well_formed_exact actual hierarchy actualBounded classesBounded]
  cases actualFormed :
      typeWellFormedReference actual hierarchy actualBounded classesBounded
  · rfl
  · rw [type_is_well_formed_exact expected hierarchy expectedBounded classesBounded]
    cases expectedFormed :
        typeWellFormedReference expected hierarchy expectedBounded classesBounded
    · rfl
    · simp only [bind_tc_ok, if_true]
      cases expected <;> simp only
      all_goals try rw [is_assignable_exact actual _ hierarchy actualBounded (by assumption)
        classesBounded remaining lengthExact]
      all_goals try simp [actualFormed, expectedFormed, assignableReference]
      case VariadicTuple element =>
        rw [type_equals_exact]
        cases elementObject : typeEqReference element .Object
        · simp
        · cases actual <;>
            simp

end TypeAlgebraKernel.Proofs
