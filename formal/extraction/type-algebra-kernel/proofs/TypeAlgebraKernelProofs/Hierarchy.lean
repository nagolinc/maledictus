import TypeAlgebraKernelProofs.Normalization

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace TypeAlgebraKernel.Proofs

open TypeAlgebraKernel
open python_type_algebra_kernel

abbrev NominalClass := python_type_algebra_kernel.NominalClass
abbrev NominalClassList := python_type_algebra_kernel.NominalClassList
abbrev NominalHierarchy := python_type_algebra_kernel.NominalHierarchy

def nominalClassListLength : NominalClassList -> Nat
  | .Empty => 0
  | .Item _ tail => nominalClassListLength tail + 1

def nominalClassListLengthReference (classes : NominalClassList) : Result Usize :=
  if bounded : nominalClassListLength classes < 2 ^ System.Platform.numBits then
    .ok (UScalar.ofNatCore (nominalClassListLength classes) bounded)
  else
    .fail .integerOverflow

/-- Exact all-input refinement of the production class-list length helper,
    including the extracted machine-integer overflow outcome. -/
theorem nominal_class_list_len_exact (classes : NominalClassList) :
    NominalClassList.len classes = nominalClassListLengthReference classes := by
  rw [NominalClassList.len.eq_def]
  cases classes with
  | Empty => simp [nominalClassListLengthReference, nominalClassListLength]
  | Item cls tail =>
      simp only
      rw [nominal_class_list_len_exact tail]
      simp only [nominalClassListLengthReference]
      by_cases tailBounded :
          nominalClassListLength tail < 2 ^ System.Platform.numBits
      · rw [dif_pos tailBounded]
        simp only [bind_tc_ok]
        change
          1#usize + Usize.ofNatCore (nominalClassListLength tail) tailBounded =
            if bounded :
                nominalClassListLength tail + 1 < 2 ^ System.Platform.numBits then
              Result.ok (Usize.ofNatCore (nominalClassListLength tail + 1) bounded)
            else
              Result.fail .integerOverflow
        by_cases resultBounded :
            nominalClassListLength tail + 1 < 2 ^ System.Platform.numBits
        · rw [dif_pos resultBounded]
          change UScalar.add (1#usize)
              (Usize.ofNatCore (nominalClassListLength tail) tailBounded) = _
          unfold UScalar.add
          have oneValue : (1#usize : Usize).val = 1 := by scalar_tac
          rw [oneValue, Usize.ofNatCore_val_eq]
          unfold UScalar.tryMk UScalar.tryMkOpt
          have checkBounded :
              UScalar.check_bounds .Usize
                  (1 + nominalClassListLength tail) = true := by
            simp
            omega
          rw [dif_pos checkBounded]
          simp [Result.ofOption, Nat.add_comm]
          apply Usize.bv_eq_imp_eq
          rfl
        · rw [dif_neg resultBounded]
          change UScalar.add (1#usize)
              (Usize.ofNatCore (nominalClassListLength tail) tailBounded) = _
          unfold UScalar.add
          have oneValue : (1#usize : Usize).val = 1 := by scalar_tac
          rw [oneValue, Usize.ofNatCore_val_eq]
          unfold UScalar.tryMk UScalar.tryMkOpt
          have checkUnbounded :
              Not (UScalar.check_bounds .Usize
                  (1 + nominalClassListLength tail) = true) := by
            simp
            omega
          rw [dif_neg checkUnbounded]
          rfl
      · rw [dif_neg tailBounded]
        have tailAtCapacity :
            2 ^ System.Platform.numBits <= nominalClassListLength tail := by
          omega
        simp [nominalClassListLength]
        omega
termination_by classes

def classParentAllReference (query : Str) : NominalClassList -> Result (Option (Option Str))
  | .Empty => .ok none
  | .Item cls tail =>
      if nameBounded : cls.name.toByteArray.size <= U32.max then
        if toStr cls.name nameBounded == query then
          match cls.parent with
          | none => .ok (some none)
          | some parent =>
              if parentBounded : parent.toByteArray.size <= U32.max then
                .ok (some (some (toStr parent parentBounded)))
              else
                .fail .panic
        else
          classParentAllReference query tail
      else
        .fail .panic

/-- Premise-free exact refinement of class lookup, including the generated
    external-model panic for owned strings that cannot be represented as `Str`. -/
theorem class_parent_all_inputs_exact
    (query : Str)
    (classes : NominalClassList) :
    class_parent query classes = classParentAllReference query classes := by
  rw [class_parent.eq_def]
  cases classes with
  | Empty => rfl
  | Item cls tail =>
      cases cls with
      | mk className parent =>
          simp only
          unfold alloc.string.String.Insts.CoreCmpPartialEqShared0Str.eq
          by_cases nameBounded : className.toByteArray.size <= U32.max
          · have nameUtf8Bounded : className.utf8ByteSize <= U32.max := by
              simpa using nameBounded
            rw [dif_pos nameBounded]
            simp only [bind_tc_ok]
            by_cases nameMatches : toStr className nameBounded == query
            · rw [if_pos nameMatches]
              cases parent with
              | none =>
                  simp [classParentAllReference, nameUtf8Bounded, nameMatches,
                    core.option.Option.as_deref]
              | some parentName =>
                  by_cases parentBounded : parentName.toByteArray.size <= U32.max
                  · have parentUtf8Bounded : parentName.utf8ByteSize <= U32.max := by
                      simpa using parentBounded
                    simp [classParentAllReference, nameUtf8Bounded, nameMatches,
                      core.option.Option.as_deref,
                      alloc.string.String.Insts.CoreOpsDerefDerefStr.deref,
                      parentUtf8Bounded]
                  · have parentUtf8Unbounded :
                        Not (parentName.utf8ByteSize <= U32.max) := by
                      simpa using parentBounded
                    simp [classParentAllReference, nameUtf8Bounded, nameMatches,
                      core.option.Option.as_deref,
                      alloc.string.String.Insts.CoreOpsDerefDerefStr.deref,
                      parentUtf8Unbounded]
            · rw [if_neg nameMatches]
              rw [class_parent_all_inputs_exact query tail]
              simp [classParentAllReference, nameUtf8Bounded, nameMatches]
          · have nameUtf8Unbounded :
                Not (className.utf8ByteSize <= U32.max) := by
              simpa using nameBounded
            rw [dif_neg nameBounded]
            simp [classParentAllReference, nameUtf8Unbounded]
termination_by classes

def subclassAllReference
    (actual expected : Str)
    (classes : NominalClassList) : Nat -> Result Bool
  | 0 => .ok false
  | fuel + 1 => do
      let parentResult <- classParentAllReference actual classes
      match parentResult with
      | some (some parent) =>
          if parent == expected then
            .ok true
          else
            subclassAllReference parent expected classes fuel
      | some none => .ok false
      | none => .ok false

theorem subclass_with_remaining_all_inputs_exact
    (actual expected : Str)
    (classes : NominalClassList)
    (remaining : Usize) :
    subclass_with_remaining actual expected classes remaining =
      subclassAllReference actual expected classes remaining.val := by
  rw [subclass_with_remaining.eq_def]
  by_cases emptyFuel : remaining = 0#usize
  · simp [emptyFuel, subclassAllReference]
  · have positiveFuel : 0 < remaining.val := by
      by_contra notPositive
      have zeroValue : remaining.val = 0 := by omega
      apply emptyFuel
      apply Usize.bv_eq_imp_eq
      scalar_tac
    rw [if_neg emptyFuel, class_parent_all_inputs_exact actual classes]
    obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positiveFuel)
    rw [fuelEq]
    simp only [subclassAllReference]
    cases parentResult : classParentAllReference actual classes with
    | fail error => simp
    | div => simp
    | ok parent =>
        cases parent with
        | none => simp
        | some parentValue =>
            cases parentValue with
            | none => simp
            | some parentName =>
                unfold Str.Insts.CoreCmpPartialEqStr.eq
                simp only [bind_tc_ok]
                by_cases parentMatches : parentName == expected
                · simp [parentMatches]
                · simp only [parentMatches, Bool.false_eq_true, if_false]
                  change (do
                    let reduced <- UScalar.sub remaining (1#usize)
                    subclass_with_remaining parentName expected classes reduced) = _
                  unfold UScalar.sub
                  simp only [UScalar.ofNatCore_val_eq]
                  rw [if_neg (by omega : Not (remaining.val < 1))]
                  simp only [bind_tc_ok]
                  rw [subclass_with_remaining_all_inputs_exact]
                  have fuelWithin : fuel < 2 ^ System.Platform.numBits := by
                    have remainingWithin :
                        remaining.val < 2 ^ System.Platform.numBits := by scalar_tac
                    omega
                  have fuelValue :
                      (BitVec.ofNat System.Platform.numBits fuel).toNat = fuel := by
                    rw [BitVec.toNat_ofNat]
                    exact Nat.mod_eq_of_lt fuelWithin
                  have decreasedValue :
                      (⟨BitVec.ofNat System.Platform.numBits fuel⟩ : Usize).val = fuel := by
                    exact fuelValue
                  have subtractionEq : remaining.val - 1 = fuel := by omega
                  rw [subtractionEq]
                  simp only [UScalarTy.Usize_numBits_eq]
                  rw [decreasedValue]
termination_by remaining.val
decreasing_by
  simp_wf
  unfold UScalar.val
  change (BitVec.ofNat System.Platform.numBits (remaining.bv.toNat - 1)).toNat <
    remaining.bv.toNat
  rw [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by scalar_tac)]
  change remaining.bv.toNat = fuel.succ at fuelEq
  omega

def subclassDecisionAllReference
    (actual expected : Str)
    (classes : NominalClassList) : Result Bool :=
  if actual == expected then
    .ok true
  else if expected == toStr "object" then
    .ok true
  else do
    let remaining <- nominalClassListLengthReference classes
    subclassAllReference actual expected classes remaining.val

def isSubclassAllReference
    (actual expected : Str)
    (hierarchy : NominalHierarchy) : Result Bool := do
  let actualParent <- classParentAllReference actual hierarchy.classes
  match actualParent with
  | none => .ok false
  | some _ =>
      if expected == toStr "object" then
        subclassDecisionAllReference actual expected hierarchy.classes
      else do
        let expectedParent <- classParentAllReference expected hierarchy.classes
        match expectedParent with
        | none => .ok false
        | some _ => subclassDecisionAllReference actual expected hierarchy.classes

/-- Premise-free exact refinement of the public nominal-subclass decision.
    The reference exposes every generated failure, including class-string
    representation panics and machine-integer overflow while counting classes. -/
theorem is_subclass_all_inputs_exact
    (actual expected : Str)
    (hierarchy : NominalHierarchy) :
    is_subclass actual expected hierarchy =
      isSubclassAllReference actual expected hierarchy := by
  unfold is_subclass
  rw [class_parent_all_inputs_exact]
  cases actualLookup : classParentAllReference actual hierarchy.classes with
  | fail error => simp [isSubclassAllReference, actualLookup]
  | div => simp [isSubclassAllReference, actualLookup]
  | ok actualParent =>
      cases actualParent with
      | none => simp [isSubclassAllReference, actualLookup]
      | some actualParentValue =>
          unfold core.cmp.impls.PartialEqShared.ne
          unfold Str.Insts.CoreCmpPartialEqStr
          simp only [core.cmp.PartialEq.ne.default]
          unfold Str.Insts.CoreCmpPartialEqStr.eq
          simp only [bind_tc_ok]
          by_cases objectExpected : expected == toStr "object"
          · have objectEq : expected = toStr "object" := by simpa using objectExpected
            simp [objectEq, actualLookup, isSubclassAllReference,
              subclassDecisionAllReference]
          · have objectNe : Not (expected = toStr "object") := by
              intro objectEq
              subst expected
              simp at objectExpected
            rw [class_parent_all_inputs_exact]
            cases expectedLookup : classParentAllReference expected hierarchy.classes with
            | fail error =>
                simp [actualLookup, expectedLookup, objectExpected,
                  isSubclassAllReference]
            | div =>
                simp [actualLookup, expectedLookup, objectExpected,
                  isSubclassAllReference]
            | ok expectedParent =>
                cases expectedParent with
                | none =>
                    simp [actualLookup, expectedLookup, objectExpected,
                      isSubclassAllReference]
                | some expectedParentValue =>
                    by_cases sameType : actual == expected
                    · have actualEq : actual = expected := by simpa using sameType
                      simp [actualEq, expectedLookup, objectExpected,
                        isSubclassAllReference, subclassDecisionAllReference]
                    · have actualNe : Not (actual = expected) := by
                        intro actualEq
                        subst actual
                        simp at sameType
                      rw [nominal_class_list_len_exact]
                      cases lengthResult : nominalClassListLengthReference hierarchy.classes with
                      | fail error =>
                          simp [actualLookup, expectedLookup, objectExpected, sameType,
                            isSubclassAllReference, subclassDecisionAllReference, lengthResult]
                      | div =>
                          simp [actualLookup, expectedLookup, objectExpected, sameType,
                            isSubclassAllReference, subclassDecisionAllReference, lengthResult]
                      | ok remaining =>
                          simp [actualNe, objectNe]
                          rw [subclass_with_remaining_all_inputs_exact]
                          simp [actualLookup, expectedLookup, objectExpected, sameType,
                            isSubclassAllReference, subclassDecisionAllReference, lengthResult]

def boundedString (value : String) : Prop :=
  value.toByteArray.size <= U32.max

def boundedParent : Option String -> Prop
  | none => True
  | some parent => boundedString parent

def boundedNominalClasses : NominalClassList -> Prop
  | .Empty => True
  | .Item cls tail =>
      boundedString cls.name /\ boundedParent cls.parent /\ boundedNominalClasses tail

def parentAsStr : (parent : Option String) -> boundedParent parent -> Option Str
  | none, _ => none
  | some parent, bounded => some (toStr parent bounded)

def classParentReference
    (query : Str) :
    (classes : NominalClassList) -> boundedNominalClasses classes -> Option (Option Str)
  | .Empty, _ => none
  | .Item cls tail, bounded =>
      if toStr cls.name bounded.1 == query then
        some (parentAsStr cls.parent bounded.2.1)
      else
        classParentReference query tail bounded.2.2

theorem class_parent_exact
    (query : Str)
    (classes : NominalClassList)
    (bounded : boundedNominalClasses classes) :
    class_parent query classes =
      .ok (classParentReference query classes bounded) := by
  rw [class_parent.eq_def]
  cases classes with
  | Empty => rfl
  | Item cls tail =>
      cases cls with
      | mk className parent =>
          change boundedString className /\
            boundedParent parent /\ boundedNominalClasses tail at bounded
          have nameBounded : className.toByteArray.size <= U32.max := bounded.1
          simp only [classParentReference]
          unfold alloc.string.String.Insts.CoreCmpPartialEqShared0Str.eq
          rw [dif_pos nameBounded]
          simp only [bind_tc_ok]
          split
          · simp only [core.option.Option.as_deref]
            cases parent with
            | none => simp [parentAsStr]
            | some parentName =>
                simp only [boundedParent] at bounded
                have parentBounded : parentName.toByteArray.size <= U32.max :=
                  bounded.2.1
                simp only [parentAsStr]
                unfold alloc.string.String.Insts.CoreOpsDerefDerefStr.deref
                rw [dif_pos parentBounded]
                simp
          · exact class_parent_exact query tail bounded.2.2
termination_by classes

def subclassReference
    (actual expected : Str)
    (classes : NominalClassList)
    (bounded : boundedNominalClasses classes) : Nat -> Bool
  | 0 => false
  | fuel + 1 =>
      match classParentReference actual classes bounded with
      | some (some parent) =>
          if parent == expected then true
          else subclassReference parent expected classes bounded fuel
      | some none | none => false

theorem subclass_with_remaining_exact
    (actual expected : Str)
    (classes : NominalClassList)
    (bounded : boundedNominalClasses classes)
    (remaining : Usize) :
    subclass_with_remaining actual expected classes remaining =
      .ok (subclassReference actual expected classes bounded remaining.val) := by
  rw [subclass_with_remaining.eq_def]
  by_cases emptyFuel : remaining = 0#usize
  · simp [emptyFuel, subclassReference]
  · have positiveFuel : 0 < remaining.val := by
      by_contra notPositive
      have zeroValue : remaining.val = 0 := by omega
      apply emptyFuel
      apply Usize.bv_eq_imp_eq
      scalar_tac
    rw [if_neg emptyFuel, class_parent_exact actual classes bounded]
    simp only [bind_tc_ok]
    obtain ⟨fuel, fuelEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positiveFuel)
    cases parentResult : classParentReference actual classes bounded with
    | none =>
        simp [parentResult, subclassReference, fuelEq]
    | some parent =>
        cases parent with
        | none =>
            simp [parentResult, subclassReference, fuelEq]
        | some parentName =>
            unfold Str.Insts.CoreCmpPartialEqStr.eq
            simp only [bind_tc_ok]
            by_cases parentMatches : parentName == expected
            · simp [parentMatches, parentResult, subclassReference, fuelEq]
            · simp only [parentMatches, Bool.false_eq_true, if_false]
              change (do
                let reduced ← UScalar.sub remaining (1#usize)
                subclass_with_remaining parentName expected classes reduced) = _
              unfold UScalar.sub
              simp only [UScalar.ofNatCore_val_eq]
              rw [if_neg (by omega : Not (remaining.val < 1))]
              simp only [bind_tc_ok]
              rw [subclass_with_remaining_exact parentName expected classes bounded]
              have fuelWithin : fuel < 2 ^ System.Platform.numBits := by
                have remainingWithin :
                    remaining.val < 2 ^ System.Platform.numBits := by scalar_tac
                omega
              have fuelValue :
                  (BitVec.ofNat System.Platform.numBits fuel).toNat = fuel := by
                rw [BitVec.toNat_ofNat]
                exact Nat.mod_eq_of_lt fuelWithin
              have decreasedValue :
                  (⟨BitVec.ofNat System.Platform.numBits fuel⟩ : Usize).val = fuel := by
                exact fuelValue
              have subtractionEq : remaining.val - 1 = fuel := by omega
              rw [subtractionEq]
              simp only [UScalarTy.Usize_numBits_eq]
              rw [decreasedValue]
              simp [subclassReference, parentResult, parentMatches, fuelEq]
termination_by remaining.val
decreasing_by
  simp_wf
  unfold UScalar.val
  change (BitVec.ofNat System.Platform.numBits (remaining.bv.toNat - 1)).toNat <
    remaining.bv.toNat
  rw [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by scalar_tac)]
  change remaining.bv.toNat = fuel.succ at fuelEq
  omega

def subclassDecisionReference
    (actual expected : Str)
    (classes : NominalClassList)
    (bounded : boundedNominalClasses classes)
    (remaining : Usize) : Bool :=
  if actual == expected then true
  else if expected == toStr "object" then true
  else subclassReference actual expected classes bounded remaining.val

def isSubclassReference
    (actual expected : Str)
    (hierarchy : NominalHierarchy)
    (bounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize) : Bool :=
  match classParentReference actual hierarchy.classes bounded with
  | none => false
  | some _ =>
      if expected == toStr "object" then
        subclassDecisionReference actual expected hierarchy.classes bounded remaining
      else
        match classParentReference expected hierarchy.classes bounded with
        | none => false
        | some _ =>
            subclassDecisionReference actual expected hierarchy.classes bounded remaining

/-- Universal exact refinement of production nominal subclassing. The two
    premises are precisely the source-representability conditions for owned
    Rust strings and the finite class-list length. -/
theorem is_subclass_exact
    (actual expected : Str)
    (hierarchy : NominalHierarchy)
    (bounded : boundedNominalClasses hierarchy.classes)
    (remaining : Usize)
    (lengthExact : NominalClassList.len hierarchy.classes = .ok remaining) :
    is_subclass actual expected hierarchy =
      .ok (isSubclassReference actual expected hierarchy bounded remaining) := by
  unfold is_subclass
  rw [class_parent_exact actual hierarchy.classes bounded]
  simp only [bind_tc_ok]
  cases actualParent : classParentReference actual hierarchy.classes bounded with
  | none => simp [actualParent, isSubclassReference]
  | some actualParentValue =>
      unfold core.cmp.impls.PartialEqShared.ne
      unfold Str.Insts.CoreCmpPartialEqStr
      simp only [core.cmp.PartialEq.ne.default]
      unfold Str.Insts.CoreCmpPartialEqStr.eq
      simp
      by_cases objectExpected : expected == toStr "object"
      · have objectEq : expected = toStr "object" := by simpa using objectExpected
        simp [objectEq, actualParent, isSubclassReference,
          subclassDecisionReference]
      · have objectNe : Not (expected = toStr "object") := by
          intro objectEq
          subst expected
          simp at objectExpected
        simp [objectNe]
        rw [class_parent_exact expected hierarchy.classes bounded]
        simp only [bind_tc_ok]
        cases expectedParent : classParentReference expected hierarchy.classes bounded with
        | none =>
            simp [expectedParent, actualParent, objectExpected, isSubclassReference]
        | some expectedParentValue =>
            simp
            by_cases sameType : actual == expected
            · have actualEq : actual = expected := by simpa using sameType
              simp [actualEq, objectExpected, expectedParent,
                isSubclassReference, subclassDecisionReference]
            · have actualNe : Not (actual = expected) := by
                intro actualEq
                subst actual
                simp at sameType
              simp [actualNe]
              rw [lengthExact]
              simp only [bind_tc_ok]
              rw [subclass_with_remaining_exact actual expected hierarchy.classes bounded]
              simp [actualNe, objectExpected, actualParent, expectedParent,
                isSubclassReference, subclassDecisionReference]

end TypeAlgebraKernel.Proofs
