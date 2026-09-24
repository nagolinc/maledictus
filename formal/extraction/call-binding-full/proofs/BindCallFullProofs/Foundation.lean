import BindCallFull

open Aeneas Aeneas.Std Result

namespace BindCallFull.Proofs

def totalIdentityClone (α : Type) : core.clone.Clone α := {
  clone := fun value => .ok value
}

def totalStringEq : core.cmp.Eq String := {
  partialEqInst := {
    eq := alloc.string.String.Insts.CoreCmpPartialEqString.eq
  }
}

theorem totalIdentityClone_exact (α : Type) (value : α) :
    (totalIdentityClone α).clone value = .ok value := by
  rfl

theorem option_clone_total_identity_exact (α : Type) (value : Option α) :
    core.option.Option.Insts.CoreCloneClone.clone (totalIdentityClone α) value = .ok value := by
  cases value <;> rfl

theorem result_err_exact {T E : Type} (value : core.result.Result T E) :
    core.result.Result.err value =
      .ok (match value with | .Ok _ => none | .Err error => some error) := by
  cases value <;> rfl

theorem string_eq_exact (left right : String) :
    alloc.string.String.Insts.CoreCmpPartialEqString.eq left right = .ok (left == right) := by
  rfl

theorem string_is_empty_exact (value : String) :
    alloc.string.String.is_empty value = .ok value.isEmpty := by
  rfl

theorem string_clone_exact (value : String) :
    alloc.string.String.Insts.CoreCloneClone.clone value = .ok value := by
  rfl

theorem compatibility_mismatch_string_exact (expected actual : String) :
    BindCallFull.compatibility_mismatch
        (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility
          totalStringEq)
        () expected actual =
      .ok (if expected == actual then false else true) := by
  by_cases equal : expected = actual <;>
    simp [BindCallFull.compatibility_mismatch,
      BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility.accepts,
      totalStringEq, alloc.string.String.Insts.CoreCmpPartialEqString.eq, equal]

theorem call_signature_default_exact (Ty Value : Type) :
    BindCallFull.CallSignature.Insts.CoreDefaultDefault.default Ty Value =
      .ok {
        positional_only := alloc.vec.Vec.new (BindCallFull.FormalParameter Ty Value)
        positional := alloc.vec.Vec.new (BindCallFull.FormalParameter Ty Value)
        keyword_only := alloc.vec.Vec.new (BindCallFull.FormalParameter Ty Value)
        var_args := none
        keyword_args := none
      } := by
  rfl

theorem exact_type_compatibility_accepts_exact
    {Ty : Type}
    (eqInst : core.cmp.Eq Ty)
    (expected actual : Ty) :
    BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility.accepts
        eqInst () expected actual =
      eqInst.partialEqInst.eq expected actual := by
  rfl

theorem callback_type_compatibility_accepts_exact
    {Ty Compatible : Type}
    (fnInst : core.ops.function.Fn Compatible (Ty × Ty) Bool)
    (callback : Compatible)
    (expected actual : Ty) :
    BindCallFull.CallbackTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility.accepts
        fnInst callback expected actual =
      fnInst.call callback (expected, actual) := by
  rfl

theorem type_compatibility_accepts_implementations_exact
    {ExactTy CallbackTy Compatible : Type}
    (eqInst : core.cmp.Eq ExactTy)
    (exactExpected exactActual : ExactTy)
    (fnInst : core.ops.function.Fn Compatible (CallbackTy × CallbackTy) Bool)
    (callback : Compatible)
    (callbackExpected callbackActual : CallbackTy) :
    (BindCallFull.ExactTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility.accepts
        eqInst () exactExpected exactActual =
      eqInst.partialEqInst.eq exactExpected exactActual) ∧
    (BindCallFull.CallbackTypeCompatibility.Insts.Maledictus_call_binding_extractionTypeCompatibility.accepts
        fnInst callback callbackExpected callbackActual =
      fnInst.call callback (callbackExpected, callbackActual)) := by
  exact ⟨rfl, rfl⟩

end BindCallFull.Proofs
