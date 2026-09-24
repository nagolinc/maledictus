import TypeAlgebraKernelProofs.Hierarchy

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace TypeAlgebraKernel.Proofs

open TypeAlgebraKernel
open python_type_algebra_kernel

mutual
  def boundedType : python_type_algebra_kernel.Type -> Prop
    | .Int => True
    | .Bool => True
    | .Str => True
    | .None => True
    | .Object => True
    | .Class className => boundedString className
    | .List element => boundedType element
    | .Set element => boundedType element
    | .VariadicTuple element => boundedType element
    | .Dict key value => boundedType key /\ boundedType value
    | .FixedTuple elements => boundedTypeList elements
    | .Union elements => boundedTypeList elements

  def boundedTypeList : python_type_algebra_kernel.TypeList -> Prop
    | .Empty => True
    | .Item ty tail => boundedType ty /\ boundedTypeList tail
end

def nominalAssignableReference
    (actual expected : String)
    (hierarchy : NominalHierarchy)
    (classesBounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize) : Bool :=
  if actualBounded : actual.toByteArray.size <= U32.max then
    if expectedBounded : expected.toByteArray.size <= U32.max then
      isSubclassReference (toStr actual actualBounded) (toStr expected expectedBounded)
        hierarchy classesBounded remaining
    else false
  else false

mutual
  def assignableValidReference
      (actual expected : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy)
      (classesBounded : boundedNominalClasses hierarchy.classes)
      (remaining : Usize) : Bool :=
    if typeEqReference actual expected then true
    else if (match expected with | .Object => true | _ => false) then true
    else
      match actual, expected with
      | .Bool, .Int => true
      | .Class actualName, .Class expectedName =>
          nominalAssignableReference actualName expectedName hierarchy classesBounded remaining
      | .Union actualTypes, expectedType =>
          everyAssignableReference actualTypes expectedType hierarchy classesBounded remaining
      | actualType, .Union expectedTypes =>
          anyAssignableReference actualType expectedTypes hierarchy classesBounded remaining
      | .FixedTuple actualTypes, .FixedTuple expectedTypes =>
          listsAssignableReference actualTypes expectedTypes hierarchy classesBounded remaining
      | .FixedTuple actualTypes, .VariadicTuple expectedType =>
          everyAssignableReference actualTypes expectedType hierarchy classesBounded remaining
      | .VariadicTuple actualType, .VariadicTuple expectedType =>
          assignableValidReference actualType expectedType hierarchy classesBounded remaining
      | _, _ => false
  termination_by typeSize actual + typeSize expected

  def everyAssignableReference
      (actual : python_type_algebra_kernel.TypeList)
      (expected : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy)
      (classesBounded : boundedNominalClasses hierarchy.classes)
      (remaining : Usize) : Bool :=
    match actual with
    | .Empty => true
    | .Item head tail =>
        assignableValidReference head expected hierarchy classesBounded remaining &&
          everyAssignableReference tail expected hierarchy classesBounded remaining
  termination_by typeListSize actual + typeSize expected

  def anyAssignableReference
      (actual : python_type_algebra_kernel.Type)
      (expected : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy)
      (classesBounded : boundedNominalClasses hierarchy.classes)
      (remaining : Usize) : Bool :=
    match expected with
    | .Empty => false
    | .Item head tail =>
        assignableValidReference actual head hierarchy classesBounded remaining ||
          anyAssignableReference actual tail hierarchy classesBounded remaining
  termination_by typeSize actual + typeListSize expected

  def listsAssignableReference
      (actual expected : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy)
      (classesBounded : boundedNominalClasses hierarchy.classes)
      (remaining : Usize) : Bool :=
    match actual, expected with
    | .Empty, .Empty => true
    | .Item actualHead actualTail, .Item expectedHead expectedTail =>
        assignableValidReference actualHead expectedHead hierarchy classesBounded remaining &&
          listsAssignableReference actualTail expectedTail hierarchy classesBounded remaining
    | _, _ => false
  termination_by typeListSize actual + typeListSize expected
  decreasing_by
    all_goals simp [typeListSize]
    all_goals omega
end

mutual
  def typeWellFormedAllReference
      (ty : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy) : Result Bool :=
    match ty with
    | .Int => .ok true
    | .Bool => .ok true
    | .Str => .ok true
    | .None => .ok true
    | .Object => .ok true
    | .Class className =>
        if nameBounded : className.toByteArray.size <= U32.max then do
          let parent <- classParentAllReference (toStr className nameBounded) hierarchy.classes
          .ok parent.isSome
        else
          .fail .panic
    | .List element => typeWellFormedAllReference element hierarchy
    | .Set element => typeWellFormedAllReference element hierarchy
    | .VariadicTuple element => typeWellFormedAllReference element hierarchy
    | .Dict key value => do
        let keyFormed <- typeWellFormedAllReference key hierarchy
        if keyFormed then typeWellFormedAllReference value hierarchy else .ok false
    | .FixedTuple elements =>
        match elements with
        | .Empty => .ok false
        | .Item _ _ => typeListWellFormedAllReference elements hierarchy
    | .Union elements =>
        match elements with
        | .Empty => .ok false
        | .Item _ _ => typeListWellFormedAllReference elements hierarchy

  def typeListWellFormedAllReference
      (types : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy) : Result Bool :=
    match types with
    | .Empty => .ok true
    | .Item ty tail => do
        let formed <- typeWellFormedAllReference ty hierarchy
        if formed then typeListWellFormedAllReference tail hierarchy else .ok false
end

mutual
  theorem type_is_well_formed_all_inputs_exact
      (ty : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy) :
      type_is_well_formed ty hierarchy = typeWellFormedAllReference ty hierarchy := by
    rw [type_is_well_formed.eq_def]
    cases ty with
    | Int => rfl
    | Bool => rfl
    | Str => rfl
    | None => rfl
    | Object => rfl
    | Class className =>
        simp only [typeWellFormedAllReference]
        unfold alloc.string.String.Insts.CoreOpsDerefDerefStr.deref
        by_cases nameBounded : className.toByteArray.size <= U32.max
        · simp only [dif_pos nameBounded, bind_tc_ok]
          rw [class_parent_all_inputs_exact]
          cases classParentAllReference (toStr className nameBounded) hierarchy.classes <;> rfl
        · simp only [dif_neg nameBounded, bind_tc_fail]
    | List element =>
        simp only [typeWellFormedAllReference]
        exact type_is_well_formed_all_inputs_exact element hierarchy
    | Set element =>
        simp only [typeWellFormedAllReference]
        exact type_is_well_formed_all_inputs_exact element hierarchy
    | VariadicTuple element =>
        simp only [typeWellFormedAllReference]
        exact type_is_well_formed_all_inputs_exact element hierarchy
    | Dict key value =>
        simp only [typeWellFormedAllReference]
        rw [type_is_well_formed_all_inputs_exact key hierarchy]
        cases typeWellFormedAllReference key hierarchy <;> simp
        case ok keyFormed =>
          cases keyFormed
          · rfl
          · exact type_is_well_formed_all_inputs_exact value hierarchy
    | FixedTuple elements =>
        cases elements with
        | Empty => rfl
        | Item head tail =>
            simp only [typeWellFormedAllReference]
            exact type_list_is_well_formed_all_inputs_exact (.Item head tail) hierarchy
    | Union elements =>
        cases elements with
        | Empty => rfl
        | Item head tail =>
            simp only [typeWellFormedAllReference]
            exact type_list_is_well_formed_all_inputs_exact (.Item head tail) hierarchy
  termination_by typeSize ty
  decreasing_by
    all_goals simp_wf

  theorem type_list_is_well_formed_all_inputs_exact
      (types : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy) :
      type_list_is_well_formed types hierarchy =
        typeListWellFormedAllReference types hierarchy := by
    rw [type_list_is_well_formed.eq_def]
    cases types with
    | Empty => rfl
    | Item ty tail =>
        simp only [typeListWellFormedAllReference]
        change (do
          let formed <- type_is_well_formed ty hierarchy
          if formed then type_list_is_well_formed tail hierarchy else .ok false) = _
        rw [type_is_well_formed_all_inputs_exact ty hierarchy]
        cases typeWellFormedAllReference ty hierarchy <;> simp
        case ok formed =>
          cases formed
          · rfl
          · exact type_list_is_well_formed_all_inputs_exact tail hierarchy
  termination_by typeListSize types
  decreasing_by
    all_goals simp_all [typeListSize]
end

def boundedClassNameStr
    (className : String)
    (bounded : boundedType (.Class className)) : Str :=
  have nameBounded : boundedString className := bounded
  toStr className nameBounded

mutual
  def typeWellFormedReference
      (ty : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy)
      (typeBounded : boundedType ty)
      (classesBounded : boundedNominalClasses hierarchy.classes) : Bool :=
    match ty with
    | .Int => true
    | .Bool => true
    | .Str => true
    | .None => true
    | .Object => true
    | .Class className =>
        (classParentReference (boundedClassNameStr className typeBounded)
          hierarchy.classes classesBounded).isSome
    | .List element =>
        typeWellFormedReference element hierarchy typeBounded classesBounded
    | .Set element =>
        typeWellFormedReference element hierarchy typeBounded classesBounded
    | .VariadicTuple element =>
        typeWellFormedReference element hierarchy typeBounded classesBounded
    | .Dict key value =>
        typeWellFormedReference key hierarchy typeBounded.1 classesBounded &&
          typeWellFormedReference value hierarchy typeBounded.2 classesBounded
    | .FixedTuple elements =>
        !typeListEqReference elements .Empty &&
          typeListWellFormedReference elements hierarchy typeBounded classesBounded
    | .Union elements =>
        !typeListEqReference elements .Empty &&
          typeListWellFormedReference elements hierarchy typeBounded classesBounded

  def typeListWellFormedReference
      (types : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy)
      (typesBounded : boundedTypeList types)
      (classesBounded : boundedNominalClasses hierarchy.classes) : Bool :=
    match types with
    | .Empty => true
    | .Item ty tail =>
        typeWellFormedReference ty hierarchy typesBounded.1 classesBounded &&
          typeListWellFormedReference tail hierarchy typesBounded.2 classesBounded
end

mutual
  theorem type_is_well_formed_exact
      (ty : python_type_algebra_kernel.Type)
      (hierarchy : NominalHierarchy)
      (typeBounded : boundedType ty)
      (classesBounded : boundedNominalClasses hierarchy.classes) :
      type_is_well_formed ty hierarchy =
        .ok (typeWellFormedReference ty hierarchy typeBounded classesBounded) := by
    rw [type_is_well_formed.eq_def]
    cases ty with
    | Int => simp only [typeWellFormedReference]
    | Bool => simp only [typeWellFormedReference]
    | Str => simp only [typeWellFormedReference]
    | None => simp only [typeWellFormedReference]
    | Object => simp only [typeWellFormedReference]
    | Class className =>
        have nameBounded : boundedString className := typeBounded
        simp only [typeWellFormedReference]
        unfold alloc.string.String.Insts.CoreOpsDerefDerefStr.deref
        change className.toByteArray.size <= U32.max at nameBounded
        rw [dif_pos nameBounded]
        simp only [bind_tc_ok]
        rw [class_parent_exact (toStr className nameBounded) hierarchy.classes classesBounded]
        have nameStrEq :
            toStr className nameBounded = boundedClassNameStr className typeBounded := by
          unfold boundedClassNameStr toStr
          rfl
        rw [nameStrEq]
        rfl
    | List element =>
        simp only [typeWellFormedReference]
        exact type_is_well_formed_exact element hierarchy typeBounded classesBounded
    | Set element =>
        simp only [typeWellFormedReference]
        exact type_is_well_formed_exact element hierarchy typeBounded classesBounded
    | VariadicTuple element =>
        simp only [typeWellFormedReference]
        exact type_is_well_formed_exact element hierarchy typeBounded classesBounded
    | Dict key value =>
        have keyBounded : boundedType key := typeBounded.1
        have valueBounded : boundedType value := typeBounded.2
        simp only [typeWellFormedReference]
        rw [type_is_well_formed_exact key hierarchy keyBounded classesBounded]
        cases typeWellFormedReference key hierarchy keyBounded classesBounded
        · rfl
        · rw [type_is_well_formed_exact value hierarchy valueBounded classesBounded]
          simp
    | FixedTuple elements =>
        have elementsBounded : boundedTypeList elements := typeBounded
        simp only [typeWellFormedReference]
        cases elements with
        | Empty => rfl
        | Item head tail =>
            rw [type_list_is_well_formed_exact (.Item head tail) hierarchy elementsBounded classesBounded]
            rfl
    | Union elements =>
        have elementsBounded : boundedTypeList elements := typeBounded
        simp only [typeWellFormedReference]
        cases elements with
        | Empty => rfl
        | Item head tail =>
            rw [type_list_is_well_formed_exact (.Item head tail) hierarchy elementsBounded classesBounded]
            rfl
  termination_by typeSize ty
  decreasing_by
    all_goals simp_wf
    all_goals simp_all [typeListSize]

  theorem type_list_is_well_formed_exact
      (types : python_type_algebra_kernel.TypeList)
      (hierarchy : NominalHierarchy)
      (typesBounded : boundedTypeList types)
      (classesBounded : boundedNominalClasses hierarchy.classes) :
      type_list_is_well_formed types hierarchy =
        .ok (typeListWellFormedReference types hierarchy typesBounded classesBounded) := by
    rw [type_list_is_well_formed.eq_def]
    cases types with
    | Empty => rfl
    | Item ty tail =>
        have tyBounded : boundedType ty := typesBounded.1
        have tailBounded : boundedTypeList tail := typesBounded.2
        simp only [typeListWellFormedReference]
        change (do
          let formed <- type_is_well_formed ty hierarchy
          if formed then type_list_is_well_formed tail hierarchy else .ok false) = _
        rw [type_is_well_formed_exact ty hierarchy tyBounded classesBounded]
        cases typeWellFormedReference ty hierarchy tyBounded classesBounded
        · rfl
        · rw [type_list_is_well_formed_exact tail hierarchy tailBounded classesBounded]
          simp
  termination_by typeListSize types
  decreasing_by
    all_goals simp_all [typeListSize]
end

end TypeAlgebraKernel.Proofs
