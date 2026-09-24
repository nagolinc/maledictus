import PersistentCollections

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace PersistentCollections.Proofs

open python_heap_contracts.python_persistent_collections

def elementKindReferenceEq : ElementKind → ElementKind → Bool
  | .Int, .Int => true
  | .Boolean, .Boolean => true
  | .Object left, .Object right => left == right
  | _, _ => false

def compatibleKindsReference
    (left right : Option ElementKind) :
    core.result.Result Unit PersistentAlgebraError :=
  match left, right with
  | some leftKind, some rightKind =>
      if elementKindReferenceEq leftKind rightKind then
        .Ok ()
      else
        .Err .ElementKindMismatch
  | _, _ => .Ok ()

theorem element_kind_clone_model (value : ElementKind) :
    ElementKind.Insts.CoreCloneClone.clone value = .ok value := by
  cases value <;>
    simp [ElementKind.Insts.CoreCloneClone.clone,
      alloc.string.String.Insts.CoreCloneClone.clone]

theorem option_element_kind_clone_model (value : Option ElementKind) :
    core.option.Option.Insts.CoreCloneClone.clone
      ElementKind.Insts.CoreCloneClone value = .ok value := by
  cases value with
  | none => rfl
  | some kind => simp [core.option.Option.Insts.CoreCloneClone.clone,
      element_kind_clone_model]

/-- Exact all-input refinement of the source-bound compatibility operation. -/
theorem require_compatible_kinds_all_inputs
    (left right : Option ElementKind) :
    require_compatible_kinds_typed left right =
      .ok (compatibleKindsReference left right) := by
  cases left with
  | none => cases right <;> rfl
  | some leftKind =>
      cases right with
      | none => rfl
      | some rightKind =>
          cases leftKind <;> cases rightKind <;>
            simp [require_compatible_kinds_typed, compatibleKindsReference,
              elementKindReferenceEq,
              alloc.string.String.Insts.CoreCmpPartialEqString.eq]
          split <;> simp_all

theorem option_or_model {T : Type} (left right : Option T) :
    core.option.Option.or left right = .ok (left.or right) := by
  cases left <;> cases right <;> rfl

theorem vec_append_success
    (left right : alloc.vec.Vec ElementValue)
    (bounded : left.val.length + right.val.length ≤ Usize.max) :
    alloc.vec.Vec.append Global left right =
      .ok (⟨left.val ++ right.val, by simp [bounded]⟩,
        alloc.vec.Vec.new ElementValue) := by
  unfold alloc.vec.Vec.append
  simp [bounded]

theorem vec_append_overflow
    (left right : alloc.vec.Vec ElementValue)
    (overflow : ¬ left.val.length + right.val.length ≤ Usize.max) :
    alloc.vec.Vec.append Global left right = .fail .panic := by
  unfold alloc.vec.Vec.append
  simp [overflow]

/-- When kinds are compatible and the real vector capacity admits the result,
    concatenation preserves exact left-to-right element order and selects the
    first present kind. -/
theorem concatenate_success_all_values
    (left right : Elements)
    (compatible : compatibleKindsReference left.kind right.kind = .Ok ())
    (bounded : left.values.val.length + right.values.val.length ≤ Usize.max) :
    concatenate_typed left right = .ok (.Ok {
      kind := left.kind.or right.kind
      values := ⟨left.values.val ++ right.values.val, by simp [bounded]⟩
    }) := by
  simp [concatenate_typed, option_element_kind_clone_model,
    require_compatible_kinds_all_inputs, compatible,
    vec_append_success _ _ bounded, option_or_model,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-- Every typed kind mismatch is propagated exactly; concatenation cannot
    erase, rewrite, or convert that diagnostic into success. -/
theorem concatenate_kind_error_all_values
    (left right : Elements) (error : PersistentAlgebraError)
    (incompatible : compatibleKindsReference left.kind right.kind = .Err error) :
    concatenate_typed left right = .ok (.Err error) := by
  simp [concatenate_typed, option_element_kind_clone_model,
    require_compatible_kinds_all_inputs, incompatible,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-- Capacity overflow remains a distinct external failure after successful
    compatibility checking; it is never collapsed into a semantic mismatch. -/
theorem concatenate_capacity_failure_all_values
    (left right : Elements)
    (compatible : compatibleKindsReference left.kind right.kind = .Ok ())
    (overflow : ¬ left.values.val.length + right.values.val.length ≤ Usize.max) :
    concatenate_typed left right = .fail .panic := by
  simp [concatenate_typed, option_element_kind_clone_model,
    require_compatible_kinds_all_inputs, compatible,
    vec_append_overflow _ _ overflow,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-- The complete concatenation partition is total for every representable
    input: compatible values either append or report capacity failure, while
    incompatible values return their typed error. -/
theorem concatenate_never_diverges (left right : Elements) :
    concatenate_typed left right ≠ .div := by
  cases observed : compatibleKindsReference left.kind right.kind with
  | Ok successValue =>
      have compatible : compatibleKindsReference left.kind right.kind = .Ok () := by
        simpa using observed
      by_cases bounded :
          left.values.val.length + right.values.val.length ≤ Usize.max
      · rw [concatenate_success_all_values left right compatible bounded]
        simp
      · rw [concatenate_capacity_failure_all_values left right compatible bounded]
        simp
  | Err error =>
      rw [concatenate_kind_error_all_values left right error observed]
      simp

/-- One public all-input refinement theorem for the complete production
    `concatenate_typed` operation. Every input is in exactly one observable
    source outcome class: typed incompatibility, exact ordered success, or the
    real representable-vector capacity failure. -/
theorem concatenate_all_inputs_exact (left right : Elements) :
    (∃ error,
      compatibleKindsReference left.kind right.kind = .Err error ∧
      concatenate_typed left right = .ok (.Err error)) ∨
    (compatibleKindsReference left.kind right.kind = .Ok () ∧
      ((left.values.val.length + right.values.val.length ≤ Usize.max ∧
        ∃ result,
          concatenate_typed left right = .ok (.Ok result) ∧
          result.kind = left.kind.or right.kind ∧
          result.values.val = left.values.val ++ right.values.val) ∨
       (¬ left.values.val.length + right.values.val.length ≤ Usize.max ∧
        concatenate_typed left right = .fail .panic))) := by
  cases observed : compatibleKindsReference left.kind right.kind with
  | Err error =>
      exact Or.inl ⟨error, rfl,
        concatenate_kind_error_all_values left right error observed⟩
  | Ok successValue =>
      cases successValue
      have compatible : compatibleKindsReference left.kind right.kind = .Ok () := by
        simpa using observed
      refine Or.inr ⟨rfl, ?_⟩
      by_cases bounded :
          left.values.val.length + right.values.val.length ≤ Usize.max
      · refine Or.inl ⟨bounded, ?_⟩
        let result : Elements := {
          kind := left.kind.or right.kind
          values := ⟨left.values.val ++ right.values.val, by simp [bounded]⟩
        }
        refine ⟨result, ?_, rfl, rfl⟩
        exact concatenate_success_all_values left right compatible bounded
      · exact Or.inr ⟨bounded,
          concatenate_capacity_failure_all_values left right compatible bounded⟩

def elementValueEqReference : ElementValue → ElementValue → Bool
  | .Int left, .Int right => decide (left = right)
  | .Boolean left, .Boolean right => decide (left = right)
  | .Object leftName leftIdentity, .Object rightName rightIdentity =>
      if decide (leftIdentity = rightIdentity) then
        leftName == rightName
      else
        false
  | _, _ => false

theorem element_value_eq_model (left right : ElementValue) :
    ElementValue.Insts.CoreCmpPartialEqElementValue.eq left right =
      .ok (elementValueEqReference left right) := by
  cases left <;> cases right <;>
    simp [ElementValue.Insts.CoreCmpPartialEqElementValue.eq,
      elementValueEqReference,
      ElementValue.read_discriminant,
      core.cmp.impls.PartialEqBool.eq,
      lift,
      alloc.string.String.Insts.CoreCmpPartialEqString.eq]
  all_goals split <;> simp_all

def containsReference (value : ElementValue) : List ElementValue → Bool
  | [] => false
  | head :: tail =>
      if elementValueEqReference value head then
        true
      else
        containsReference value tail

theorem list_anyM_element_value_model
    (values : List ElementValue) (value : ElementValue) :
    List.anyM (ElementValue.Insts.CoreCmpPartialEqElementValue.eq value) values =
      .ok (containsReference value values) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      rw [List.anyM, element_value_eq_model]
      cases present : elementValueEqReference value head with
      | false => simp [containsReference, present, induction]
      | true =>
          simp only [containsReference, present, if_true]
          rfl

theorem slice_contains_model (values : Slice ElementValue) (value : ElementValue) :
    core.slice.Slice.contains
        ElementValue.Insts.CoreCmpPartialEqElementValue values value =
      .ok (containsReference value values.val) := by
  exact list_anyM_element_value_model values.val value

def uniqueReference : List ElementValue → List ElementValue → List ElementValue
  | [], accumulated => accumulated
  | value :: remaining, accumulated =>
      if containsReference value accumulated then
        uniqueReference remaining accumulated
      else
        uniqueReference remaining (accumulated ++ [value])

/-- Exact all-input refinement and termination of the extracted loop used by
    the production `unique` function. The only bound is the real representable
    `Vec` capacity carried by the extracted input. -/
theorem unique_loop_exact :
    (values : List ElementValue) →
    (valuesBound : values.length ≤ Usize.max) →
    (unique : alloc.vec.Vec ElementValue) →
    (bounded : unique.val.length + values.length ≤ Usize.max) →
    ∃ result,
      unique_loop
          (⟨values, valuesBound⟩ : alloc.vec.into_iter.IntoIter ElementValue)
          unique = .ok result ∧
      result.val = uniqueReference values unique.val
  | [], valuesBound, unique, bounded => by
      rw [unique_loop, loop.eq_def]
      simp only
      refine ⟨unique, ?_, ?_⟩
      · rfl
      · rfl
  | value :: remaining, valuesBound, unique, bounded => by
      rw [unique_loop, loop.eq_def]
      simp only
      have remainingBound : remaining.length ≤ Usize.max :=
        Nat.le_of_lt (by simpa using valuesBound)
      have boundedClean : unique.val.length + (remaining.length + 1) ≤ Usize.max := by
        simpa using bounded
      let remainingIter : alloc.vec.into_iter.IntoIter ElementValue :=
        ⟨remaining, remainingBound⟩
      have bodyModel :
          unique_loop.body
              (⟨value :: remaining, valuesBound⟩ :
                alloc.vec.into_iter.IntoIter ElementValue) unique =
            (if containsReference value unique.val then
              .ok (.cont (remainingIter, unique))
            else do
              let extended ← alloc.vec.Vec.push unique value
              ok (.cont (remainingIter, extended))) := by
        simp [unique_loop.body, alloc.vec.into_iter.IteratorIntoIter.next,
          alloc.vec.Vec.deref, remainingIter]
        rw [slice_contains_model]
        rfl
      erw [bodyModel]
      cases alreadyPresent : containsReference value unique.val with
      | false =>
        have uniqueBound : unique.val.length < Usize.max := by omega
        let extended : alloc.vec.Vec ElementValue :=
          ⟨unique.val ++ [value], by simp; omega⟩
        have pushModel : alloc.vec.Vec.push unique value = .ok extended := by
          unfold alloc.vec.Vec.push
          simp [extended, uniqueBound]
        rw [pushModel]
        simp only [bind_tc_ok]
        have recursive := unique_loop_exact
          remaining remainingBound extended (by simp [extended]; omega)
        simpa [uniqueReference, alreadyPresent, unique_loop, remainingIter]
          using recursive
      | true =>
        have recursive := unique_loop_exact
          remaining remainingBound unique (by omega)
        simpa [uniqueReference, alreadyPresent, unique_loop, remainingIter]
          using recursive
termination_by values => values.length

/-- Exact all-input correspondence and termination for the extracted production
    `unique` function. The output retains the source kind and is precisely the
    first-occurrence, left-to-right de-duplication of the source values. -/
theorem unique_all_inputs_exact (elements : Elements) :
    ∃ result,
      unique elements = .ok result ∧
      result.kind = elements.kind ∧
      result.values.val = uniqueReference elements.values.val [] := by
  have loopResult := unique_loop_exact elements.values.val elements.values.property
    (alloc.vec.Vec.new ElementValue) (by simpa using elements.values.property)
  obtain ⟨deduplicated, loopEquation, valuesEquation⟩ := loopResult
  refine ⟨{ elements with values := deduplicated }, ?_, rfl, valuesEquation⟩
  unfold unique
  rw [alloc.vec.IntoIteratorVec.into_iter]
  simp only [bind_tc_ok]
  change (do
    let result ← unique_loop
      (⟨elements.values.val, elements.values.property⟩ :
        alloc.vec.into_iter.IntoIter ElementValue)
      (alloc.vec.Vec.new ElementValue)
    ok { elements with values := result }) =
      ok { elements with values := deduplicated }
  rw [loopEquation]
  rfl

end PersistentCollections.Proofs
