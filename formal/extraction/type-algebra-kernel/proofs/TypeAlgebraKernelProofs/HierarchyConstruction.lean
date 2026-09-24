import TypeAlgebraHierarchy.Code.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace TypeAlgebraKernel.Proofs

namespace NominalConstruction

open TypeAlgebraHierarchy
open TypeAlgebraHierarchy.python_type_algebra_kernel

deriving instance Inhabited for NominalClass

def prependNominalClasses :
    List NominalClass → NominalClassList → NominalClassList :=
  fun values tail => values.foldr NominalClassList.Item tail

theorem nominalClassList_from_vec_loop_exact_hierarchy
    (values : List NominalClass)
    (bounded : values.length ≤ Usize.max)
    (result : NominalClassList) :
    NominalClassList.from_vec_loop
        ({ val := values, property := bounded } : alloc.vec.Vec NominalClass)
        result = .ok (prependNominalClasses values result) := by
  induction values using List.reverseRecOn generalizing result with
  | nil =>
      rw [NominalClassList.from_vec_loop.eq_def, loop.eq_def]
      simp [NominalClassList.from_vec_loop.body,
        alloc.vec.Vec.pop, prependNominalClasses]
  | append_singleton items finalClass induction =>
      rw [NominalClassList.from_vec_loop.eq_def, loop.eq_def]
      simp only
      have itemsBounded : items.length ≤ Usize.max := by
        have shorter : items.length ≤ (items ++ [finalClass]).length := by simp
        exact shorter.trans bounded
      have popped :
          alloc.vec.Vec.pop Global
              ({ val := items ++ [finalClass], property := bounded } :
                alloc.vec.Vec NominalClass) =
            .ok (some finalClass,
              ({ val := items, property := itemsBounded } :
                alloc.vec.Vec NominalClass)) := by
        unfold alloc.vec.Vec.pop
        simp
      rw [NominalClassList.from_vec_loop.body, popped]
      simp only [bind_tc_ok]
      have recursive := induction itemsBounded (.Item finalClass result)
      simpa [NominalClassList.from_vec_loop, prependNominalClasses,
        List.foldr_append] using recursive

theorem nominalClassList_from_vec_exact_hierarchy
    (classes : alloc.vec.Vec NominalClass) :
    NominalClassList.from_vec classes =
      .ok (prependNominalClasses classes.val .Empty) := by
  exact nominalClassList_from_vec_loop_exact_hierarchy
    classes.val classes.property .Empty

def classNamesEqual (left right : NominalClass) : Bool :=
  left.name == right.name

def nameOccurs (classes : List NominalClass) (queryName : String) : Bool :=
  classes.any (fun candidate => candidate.name == queryName)

def duplicateBefore
    (classes : List NominalClass) (index : Nat) (queryName : String) : Bool :=
  (classes.take index).any (fun candidate => candidate.name == queryName)

def parentResolves
    (classes : List NominalClass) (objectName : String) : Option String → Bool
  | none => true
  | some parent => (parent == objectName) || nameOccurs classes parent

def classEntryValid
    (classes : List NominalClass) (objectName : String)
    (index : Nat) (entry : NominalClass) : Bool :=
  (entry.name != objectName) &&
    (!duplicateBefore classes index entry.name) &&
    parentResolves classes objectName entry.parent

def validationPhaseOne (classes : List NominalClass) (objectName : String) : Bool :=
  (classes.zipIdx.all fun entryAndIndex =>
    classEntryValid classes objectName entryAndIndex.2 entryAndIndex.1)

def lastParentIndex (classes : List NominalClass) (parentName : String) : Nat :=
  (classes.zipIdx.foldl
    (fun selected entryAndIndex =>
      if entryAndIndex.1.name == parentName then entryAndIndex.2 else selected)
    0)

def parentWalk
    (classes : List NominalClass) (objectName : String) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, current =>
      match classes[current]? with
      | none => false
      | some entry =>
          match entry.parent with
          | none => true
          | some parent =>
              if parent == objectName then true
              else parentWalk classes objectName fuel (lastParentIndex classes parent)

def validationPhaseTwo (classes : List NominalClass) (objectName : String) : Bool :=
  (List.range classes.length).all fun index =>
    parentWalk classes objectName (classes.length + 1) index

def validateNominalHierarchyReference (classes : List NominalClass) : Bool :=
  let objectName := "object"
  validationPhaseOne classes objectName && validationPhaseTwo classes objectName

def scanDuplicateReference
    (classes : List NominalClass) (queryName : String) : Nat → Nat → Bool → Bool
  | 0, _, duplicate => duplicate
  | remaining + 1, cursor, duplicate =>
      let duplicate' := duplicate ||
        (classes[cursor]!.name == queryName)
      scanDuplicateReference classes queryName remaining (cursor + 1) duplicate'

def duplicateScanRemaining (index : Usize) (state : Bool × Usize) : Nat :=
  index.val - state.2.val

def duplicateScanInvariant
    (classes : Slice NominalClass) (index : Usize) (queryName : String)
    (expected : Bool) (state : Bool × Usize) : Prop :=
  state.2.val ≤ index.val ∧
    scanDuplicateReference classes.val queryName
      (index.val - state.2.val) state.2.val state.1 = expected

theorem validate_loop0_loop0_body_exact
    (classes : Slice NominalClass) (index : Usize) (queryName : String)
    (expected : Bool) (state : Bool × Usize)
    (hIndex : index.val ≤ classes.val.length)
    (invariant : duplicateScanInvariant classes index queryName expected state) :
    WP.spec
      (validate_nominal_hierarchy_loop0_loop0.body
        classes index queryName state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output = expected
        | .cont next =>
            duplicateScanInvariant classes index queryName expected next ∧
              duplicateScanRemaining index next < duplicateScanRemaining index state) := by
  rcases state with ⟨duplicate, priorIndex⟩
  unfold validate_nominal_hierarchy_loop0_loop0.body
  unfold duplicateScanInvariant at invariant ⊢
  unfold duplicateScanRemaining
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  by_cases within : priorIndex < index
  · simp only [within, if_true]
    have natWithin : priorIndex.val < index.val := by simpa using within
    have inBounds : priorIndex.val < classes.val.length :=
      natWithin.trans_le hIndex
    by_cases alreadyDuplicate : duplicate = true
    · simp only [alreadyDuplicate, if_true]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        have sliceBound := classes.property
        omega
      simp only [nextIndexEq]
      refine ⟨by omega, ?_, by omega⟩
      have positiveRemaining : 0 < index.val - priorIndex.val := by omega
      cases remainingEq : index.val - priorIndex.val with
      | zero => omega
      | succ remaining =>
          have nextRemaining : index.val - (priorIndex.val + 1) = remaining := by omega
          simpa [scanDuplicateReference, remainingEq, alreadyDuplicate,
            nextRemaining] using invariant.2
    · have duplicateFalse : duplicate = false := Bool.eq_false_of_not_eq_true alreadyDuplicate
      simp only [duplicateFalse, Bool.false_eq_true, if_false]
      step with Slice.index_usize_spec as ⟨entry, entryEq⟩ by
        exact inBounds
      rw [alloc.string.String.Insts.CoreCmpPartialEqString.eq]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩ by
        have sliceBound := classes.property
        omega
      simp only [entryEq, nextIndexEq]
      refine ⟨by omega, ?_, by omega⟩
      have positiveRemaining : 0 < index.val - priorIndex.val := by omega
      cases remainingEq : index.val - priorIndex.val with
      | zero => omega
      | succ remaining =>
          have nextRemaining : index.val - (priorIndex.val + 1) = remaining := by omega
          have entryBang : classes.val[priorIndex.val]!.name =
              classes.val[priorIndex.val].name := by
            simp [inBounds]
          have recursiveEq :
              scanDuplicateReference classes.val queryName remaining
                (priorIndex.val + 1)
                (classes.val[priorIndex.val]!.name == queryName) = expected := by
            simpa [scanDuplicateReference, remainingEq, duplicateFalse] using invariant.2
          rw [entryBang] at recursiveEq
          simpa [nextRemaining] using recursiveEq
  · simp only [within, if_false]
    have exhausted : index.val ≤ priorIndex.val := by simpa using Nat.le_of_not_gt within
    have atEnd : priorIndex.val = index.val := by omega
    simpa [atEnd, scanDuplicateReference] using invariant.2

theorem validate_loop0_loop0_spec
    (classes : Slice NominalClass)
    (index priorIndex : Usize)
    (queryName : String)
    (duplicate : Bool)
    (hPrior : priorIndex.val ≤ index.val)
    (hIndex : index.val ≤ classes.val.length) :
    WP.spec
      (validate_nominal_hierarchy_loop0_loop0
        classes index queryName duplicate priorIndex)
      (fun output => output = scanDuplicateReference classes.val queryName
        (index.val - priorIndex.val) priorIndex.val duplicate) := by
  let expected := scanDuplicateReference classes.val queryName
    (index.val - priorIndex.val) priorIndex.val duplicate
  have initialInvariant :
      duplicateScanInvariant classes index queryName expected (duplicate, priorIndex) :=
    ⟨hPrior, rfl⟩
  unfold validate_nominal_hierarchy_loop0_loop0
  apply loop.spec_decr_nat
      (measure := duplicateScanRemaining index)
      (inv := duplicateScanInvariant classes index queryName expected)
      (post := fun output => output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (validate_loop0_loop0_body_exact
      classes index queryName expected state hIndex stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem result_eq_ok_of_spec_eq {T : Type} (result : Result T) (expected : T)
    (spec : WP.spec result (fun output => output = expected)) :
    result = .ok expected := by
  cases result <;> simp_all [WP.spec, WP.theta, WP.wp_return]

theorem usize_sub_value_spec {x y : Usize} (h : y.val ≤ x.val) :
    WP.spec (x - y) (fun output => output.val = x.val - y.val) := by
  apply WP.spec_mono (Std.Usize.sub_spec h)
  intro output post
  exact post.1

theorem validate_loop0_loop0_exact
    (classes : Slice NominalClass)
    (index priorIndex : Usize)
    (queryName : String)
    (duplicate : Bool)
    (hPrior : priorIndex.val ≤ index.val)
    (hIndex : index.val ≤ classes.val.length) :
    validate_nominal_hierarchy_loop0_loop0
        classes index queryName duplicate priorIndex =
      .ok (scanDuplicateReference classes.val queryName
        (index.val - priorIndex.val) priorIndex.val duplicate) := by
  exact result_eq_ok_of_spec_eq _ _
    (validate_loop0_loop0_spec
      classes index priorIndex queryName duplicate hPrior hIndex)

def nameScanRemaining (classes : Slice NominalClass) (state : Bool × Usize) : Nat :=
  classes.val.length - state.2.val

def nameScanInvariant
    (classes : Slice NominalClass) (queryName : String)
    (expected : Bool) (state : Bool × Usize) : Prop :=
  state.2.val ≤ classes.val.length ∧
    scanDuplicateReference classes.val queryName
      (classes.val.length - state.2.val) state.2.val state.1 = expected

theorem validate_loop0_loop1_body_exact
    (classes : Slice NominalClass) (queryName : String)
    (expected : Bool) (state : Bool × Usize)
    (invariant : nameScanInvariant classes queryName expected state) :
    WP.spec
      (validate_nominal_hierarchy_loop0_loop1.body
        classes queryName state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output = expected
        | .cont next =>
            nameScanInvariant classes queryName expected next ∧
              nameScanRemaining classes next < nameScanRemaining classes state) := by
  rcases state with ⟨found, candidateIndex⟩
  unfold validate_nominal_hierarchy_loop0_loop1.body
  unfold nameScanInvariant at invariant ⊢
  unfold nameScanRemaining
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  by_cases within : candidateIndex < Slice.len classes
  · simp [within]
    have inBounds : candidateIndex.val < classes.val.length := by
      simpa [Slice.len] using within
    by_cases alreadyFound : found = true
    · simp only [alreadyFound, if_true]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩
      simp only [nextIndexEq]
      refine ⟨by omega, ?_, by omega⟩
      have positiveRemaining : 0 < classes.val.length - candidateIndex.val := by omega
      cases remainingEq : classes.val.length - candidateIndex.val with
      | zero => omega
      | succ remaining =>
          have nextRemaining :
              classes.val.length - (candidateIndex.val + 1) = remaining := by omega
          simpa [scanDuplicateReference, remainingEq, alreadyFound,
            nextRemaining] using invariant.2
    · have foundFalse : found = false := Bool.eq_false_of_not_eq_true alreadyFound
      simp only [foundFalse, Bool.false_eq_true, if_false]
      step with Slice.index_usize_spec as ⟨entry, entryEq⟩
      rw [alloc.string.String.Insts.CoreCmpPartialEqString.eq]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩
      simp only [entryEq, nextIndexEq]
      refine ⟨by omega, ?_, by omega⟩
      have positiveRemaining : 0 < classes.val.length - candidateIndex.val := by omega
      cases remainingEq : classes.val.length - candidateIndex.val with
      | zero => omega
      | succ remaining =>
          have nextRemaining :
              classes.val.length - (candidateIndex.val + 1) = remaining := by omega
          have entryBang : classes.val[candidateIndex.val]!.name =
              classes.val[candidateIndex.val].name := by simp [inBounds]
          have recursiveEq :
              scanDuplicateReference classes.val queryName remaining
                (candidateIndex.val + 1)
                (classes.val[candidateIndex.val]!.name == queryName) = expected := by
            simpa [scanDuplicateReference, remainingEq, foundFalse] using invariant.2
          rw [entryBang] at recursiveEq
          simpa [nextRemaining] using recursiveEq
  · simp only [within, if_false]
    have exhausted : classes.val.length ≤ candidateIndex.val := by
      simpa [Slice.len] using Nat.le_of_not_gt within
    have atEnd : candidateIndex.val = classes.val.length := by omega
    simpa [atEnd, scanDuplicateReference] using invariant.2

theorem validate_loop0_loop1_spec
    (classes : Slice NominalClass) (found : Bool)
    (queryName : String) (candidateIndex : Usize)
    (hIndex : candidateIndex.val ≤ classes.val.length) :
    WP.spec
      (validate_nominal_hierarchy_loop0_loop1
        classes found queryName candidateIndex)
      (fun output => output = scanDuplicateReference classes.val queryName
        (classes.val.length - candidateIndex.val) candidateIndex.val found) := by
  let expected := scanDuplicateReference classes.val queryName
    (classes.val.length - candidateIndex.val) candidateIndex.val found
  have initialInvariant :
      nameScanInvariant classes queryName expected (found, candidateIndex) :=
    ⟨hIndex, rfl⟩
  unfold validate_nominal_hierarchy_loop0_loop1
  apply loop.spec_decr_nat
      (measure := nameScanRemaining classes)
      (inv := nameScanInvariant classes queryName expected)
      (post := fun output => output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (validate_loop0_loop1_body_exact classes queryName expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem validate_loop0_loop1_exact
    (classes : Slice NominalClass) (found : Bool)
    (queryName : String) (candidateIndex : Usize)
    (hIndex : candidateIndex.val ≤ classes.val.length) :
    validate_nominal_hierarchy_loop0_loop1
        classes found queryName candidateIndex =
      .ok (scanDuplicateReference classes.val queryName
        (classes.val.length - candidateIndex.val) candidateIndex.val found) := by
  exact result_eq_ok_of_spec_eq _ _
    (validate_loop0_loop1_spec classes found queryName candidateIndex hIndex)

def classEntryValidScan
    (classes : List NominalClass) (objectName : String)
    (index : Nat) (entry : NominalClass) : Bool :=
  let duplicate := scanDuplicateReference classes entry.name index 0 false
  let parentResolves := match entry.parent with
    | none => true
    | some parent =>
        (parent == objectName) ||
          scanDuplicateReference classes parent classes.length 0 false
  (!(entry.name == objectName)) && (!duplicate) && parentResolves

def phaseOneScanReference
    (classes : List NominalClass) (objectName : String) : Nat → Nat → Bool → Bool
  | 0, _, valid => valid
  | remaining + 1, index, valid =>
      let nextValid := valid &&
        classEntryValidScan classes objectName index classes[index]!
      phaseOneScanReference classes objectName remaining (index + 1) nextValid

def phaseOneRemaining (classes : Slice NominalClass) (state : Bool × Usize) : Nat :=
  classes.val.length - state.2.val

def phaseOneInvariant
    (classes : Slice NominalClass) (objectName : String)
    (expected : Bool) (state : Bool × Usize) : Prop :=
  state.2.val ≤ classes.val.length ∧
    phaseOneScanReference classes.val objectName
      (classes.val.length - state.2.val) state.2.val state.1 = expected

theorem validate_loop0_body_exact
    (classes : Slice NominalClass) (objectName : String)
    (expected : Bool) (state : Bool × Usize)
    (invariant : phaseOneInvariant classes objectName expected state) :
    WP.spec
      (validate_nominal_hierarchy_loop0.body
        classes objectName state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output = expected
        | .cont next =>
            phaseOneInvariant classes objectName expected next ∧
              phaseOneRemaining classes next < phaseOneRemaining classes state) := by
  rcases state with ⟨valid, index⟩
  unfold validate_nominal_hierarchy_loop0.body
  unfold phaseOneInvariant at invariant ⊢
  unfold phaseOneRemaining
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  by_cases within : index < Slice.len classes
  · simp [within]
    have inBounds : index.val < classes.val.length := by
      simpa [Slice.len] using within
    have indexBound : index.val ≤ classes.val.length := by omega
    have bangEq : classes.val[index.val]! = classes.val[index.val] := by simp [inBounds]
    by_cases stillValid : valid = true
    · simp only [stillValid, if_true]
      step with Slice.index_usize_spec as ⟨entry, entryEq⟩
      rw [alloc.string.String.Insts.CoreCloneClone.clone]
      simp only [bind_tc_ok]
      rw [validate_loop0_loop0_exact classes index 0#usize entry.name false (by simp)
        indexBound]
      simp only [bind_tc_ok]
      step with Slice.index_usize_spec as ⟨entryAgain, entryAgainEq⟩
      rw [core.option.Option.Insts.CoreCloneClone.clone.eq_def]
      cases parentEq : entryAgain.parent with
      | none =>
          have classParentEq : classes.val[index.val].parent = none := by
            simpa [entryAgainEq] using parentEq
          simp only [bind_tc_ok, core.option.Option.is_none, Bool.not_false,
            alloc.string.String.Insts.CoreCmpPartialEqString.eq]
          step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩
          simp only [entryEq, entryAgainEq, nextIndexEq]
          refine ⟨by omega, ?_, by omega⟩
          have positiveRemaining : 0 < classes.val.length - index.val := by omega
          cases remainingEq : classes.val.length - index.val with
          | zero => omega
          | succ remaining =>
              have nextRemaining :
                  classes.val.length - (index.val + 1) = remaining := by omega
              simpa [phaseOneScanReference, remainingEq, nextRemaining,
                classEntryValidScan, bangEq, classParentEq, stillValid] using invariant.2
      | some parentName =>
          have classParentEq : classes.val[index.val].parent = some parentName := by
            simpa [entryAgainEq] using parentEq
          simp only [bind_tc_ok, core.option.Option.is_none, Bool.not_true,
            alloc.string.String.Insts.CoreCmpPartialEqString.eq]
          rw [alloc.string.String.Insts.CoreCloneClone.clone]
          simp only [bind_tc_ok]
          by_cases parentIsObject : (parentName == objectName) = true
          · rw [if_pos parentIsObject]
            step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩
            simp only [entryEq, entryAgainEq, nextIndexEq]
            refine ⟨by omega, ?_, by omega⟩
            have positiveRemaining : 0 < classes.val.length - index.val := by omega
            cases remainingEq : classes.val.length - index.val with
            | zero => omega
            | succ remaining =>
                have nextRemaining :
                    classes.val.length - (index.val + 1) = remaining := by omega
                simpa [phaseOneScanReference, remainingEq, nextRemaining,
                  classEntryValidScan, bangEq, classParentEq, parentIsObject,
                  stillValid] using invariant.2
          · have parentNotObject : (parentName == objectName) = false :=
              Bool.eq_false_of_not_eq_true parentIsObject
            rw [if_neg parentIsObject]
            rw [validate_loop0_loop1_exact classes false parentName 0#usize (by simp)]
            simp only [bind_tc_ok]
            step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩
            simp only [entryEq, entryAgainEq, nextIndexEq]
            refine ⟨by omega, ?_, by omega⟩
            have positiveRemaining : 0 < classes.val.length - index.val := by omega
            cases remainingEq : classes.val.length - index.val with
            | zero => omega
            | succ remaining =>
                have nextRemaining :
                    classes.val.length - (index.val + 1) = remaining := by omega
                simpa [phaseOneScanReference, remainingEq, nextRemaining,
                  classEntryValidScan, bangEq, classParentEq, parentNotObject,
                  stillValid] using invariant.2
    · have invalid : valid = false := Bool.eq_false_of_not_eq_true stillValid
      simp [invalid]
      step with Std.Usize.add_spec as ⟨nextIndex, nextIndexEq⟩
      simp only [nextIndexEq]
      refine ⟨by omega, ?_, by omega⟩
      have positiveRemaining : 0 < classes.val.length - index.val := by omega
      cases remainingEq : classes.val.length - index.val with
      | zero => omega
      | succ remaining =>
          have nextRemaining :
              classes.val.length - (index.val + 1) = remaining := by omega
          simpa [phaseOneScanReference, remainingEq, nextRemaining, invalid] using invariant.2
  · simp [within]
    have exhausted : classes.val.length ≤ index.val := by
      simpa [Slice.len] using Nat.le_of_not_gt within
    have atEnd : index.val = classes.val.length := by omega
    simpa [atEnd, phaseOneScanReference] using invariant.2

theorem validate_loop0_spec
    (classes : Slice NominalClass) (objectName : String)
    (valid : Bool) (index : Usize)
    (hIndex : index.val ≤ classes.val.length) :
    WP.spec (validate_nominal_hierarchy_loop0 classes objectName valid index)
      (fun output => output = phaseOneScanReference classes.val objectName
        (classes.val.length - index.val) index.val valid) := by
  let expected := phaseOneScanReference classes.val objectName
    (classes.val.length - index.val) index.val valid
  have initialInvariant : phaseOneInvariant classes objectName expected (valid, index) :=
    ⟨hIndex, rfl⟩
  unfold validate_nominal_hierarchy_loop0
  apply loop.spec_decr_nat
      (measure := phaseOneRemaining classes)
      (inv := phaseOneInvariant classes objectName expected)
      (post := fun output => output = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (validate_loop0_body_exact classes objectName expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem validate_loop0_exact
    (classes : Slice NominalClass) (objectName : String)
    (valid : Bool) (index : Usize)
    (hIndex : index.val ≤ classes.val.length) :
    validate_nominal_hierarchy_loop0 classes objectName valid index =
      .ok (phaseOneScanReference classes.val objectName
        (classes.val.length - index.val) index.val valid) := by
  exact result_eq_ok_of_spec_eq _ _
    (validate_loop0_spec classes objectName valid index hIndex)

def lastIndexScanReference
    (classes : List NominalClass) (queryName : String) : Nat → Nat → Nat → Nat
  | 0, _, selected => selected
  | remaining + 1, cursor, selected =>
      let nextSelected := if classes[cursor]!.name == queryName then cursor else selected
      lastIndexScanReference classes queryName remaining (cursor + 1) nextSelected

def lastIndexRemaining (classes : Slice NominalClass) (state : Usize × Usize) : Nat :=
  classes.val.length - state.2.val

def lastIndexInvariant
    (classes : Slice NominalClass) (queryName : String)
    (expected : Nat) (state : Usize × Usize) : Prop :=
  state.1.val ≤ classes.val.length ∧ state.2.val ≤ classes.val.length ∧
    lastIndexScanReference classes.val queryName
      (classes.val.length - state.2.val) state.2.val state.1.val = expected

theorem validate_loop1_loop0_loop0_body_exact
    (classes : Slice NominalClass) (queryName : String)
    (expected : Nat) (state : Usize × Usize)
    (invariant : lastIndexInvariant classes queryName expected state) :
    WP.spec
      (validate_nominal_hierarchy_loop1_loop0_loop0.body
        classes queryName state.1 state.2)
      (fun flow =>
        match flow with
        | .done output => output.val = expected
        | .cont next =>
            lastIndexInvariant classes queryName expected next ∧
              lastIndexRemaining classes next < lastIndexRemaining classes state) := by
  rcases state with ⟨selected, candidateIndex⟩
  unfold validate_nominal_hierarchy_loop1_loop0_loop0.body
  unfold lastIndexInvariant at invariant ⊢
  unfold lastIndexRemaining
  simp only [Prod.fst, Prod.snd] at invariant ⊢
  by_cases within : candidateIndex < Slice.len classes
  · simp only [within, if_true]
    have inBounds : candidateIndex.val < classes.val.length := by
      simpa [Slice.len] using within
    step with Slice.index_usize_spec as ⟨entry, entryEq⟩
    rw [alloc.string.String.Insts.CoreCmpPartialEqString.eq]
    by_cases isMatch : (entry.name == queryName) = true
    · simp only [isMatch, bind_tc_ok]
      have castOneEq : UScalar.cast_fromBool .Usize true = 1#usize := by
        apply UScalar.eq_of_val_eq
        simp
      rw [castOneEq]
      simp only [lift, bind_tc_ok]
      step with Std.Usize.mul_spec as ⟨left, leftEq⟩ by
        change candidateIndex.val ≤ Usize.max
        exact invariant.2.1.trans classes.property
      rw [show (1#usize - 1#usize : Result Usize) = .ok 0#usize by
        change UScalar.sub 1#usize 1#usize = .ok 0#usize
        simp [UScalar.sub]
        apply UScalar.eq_of_val_eq
        apply UScalar.ofNatCore_val_eq]
      simp only [bind_tc_ok]
      step with Std.Usize.mul_spec as ⟨right, rightEq⟩ by scalar_tac
      step with Std.Usize.add_spec as ⟨nextSelected, nextSelectedEq⟩ by scalar_tac
      step with Std.Usize.add_spec as ⟨nextCandidate, nextCandidateEq⟩
      simp only [leftEq, rightEq, nextSelectedEq, nextCandidateEq,
        Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
      refine ⟨by omega, by omega, ?_, by omega⟩
      have positiveRemaining : 0 < classes.val.length - candidateIndex.val := by omega
      cases remainingEq : classes.val.length - candidateIndex.val with
      | zero => omega
      | succ remaining =>
          have nextRemaining :
              classes.val.length - (candidateIndex.val + 1) = remaining := by omega
          have entryBang : classes.val[candidateIndex.val]!.name =
              classes.val[candidateIndex.val].name := by simp [inBounds]
          have classNameEq : classes.val[candidateIndex.val].name = queryName := by
            simpa [entryEq] using isMatch
          have recursiveEq :
              lastIndexScanReference classes.val queryName remaining
                (candidateIndex.val + 1)
                (if classes.val[candidateIndex.val]!.name = queryName
                  then candidateIndex.val else selected.val) = expected := by
            simpa [lastIndexScanReference, remainingEq] using invariant.2.2
          rw [entryBang] at recursiveEq
          simpa [nextRemaining, classNameEq] using recursiveEq
    · have notMatches : (entry.name == queryName) = false :=
        Bool.eq_false_of_not_eq_true isMatch
      simp only [notMatches, bind_tc_ok]
      have castZeroEq : UScalar.cast_fromBool .Usize false = 0#usize := by
        apply UScalar.eq_of_val_eq
        simp
      rw [castZeroEq]
      simp only [lift, bind_tc_ok]
      step with Std.Usize.mul_spec as ⟨left, leftEq⟩ by
        change 0 ≤ Usize.max
        omega
      rw [show (1#usize - 0#usize : Result Usize) = .ok 1#usize by
        change UScalar.sub 1#usize 0#usize = .ok 1#usize
        simp [UScalar.sub]
        apply Usize.bv_eq_imp_eq
        apply BitVec.eq_of_toNat_eq
        simp [UScalar.val]]
      simp only [bind_tc_ok]
      step with Std.Usize.mul_spec as ⟨right, rightEq⟩ by scalar_tac
      step with Std.Usize.add_spec as ⟨nextSelected, nextSelectedEq⟩ by scalar_tac
      step with Std.Usize.add_spec as ⟨nextCandidate, nextCandidateEq⟩
      simp only [leftEq, rightEq, nextSelectedEq, nextCandidateEq,
        Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
      refine ⟨invariant.1, by omega, ?_, by omega⟩
      have positiveRemaining : 0 < classes.val.length - candidateIndex.val := by omega
      cases remainingEq : classes.val.length - candidateIndex.val with
      | zero => omega
      | succ remaining =>
          have nextRemaining :
              classes.val.length - (candidateIndex.val + 1) = remaining := by omega
          have entryBang : classes.val[candidateIndex.val]!.name =
              classes.val[candidateIndex.val].name := by simp [inBounds]
          have classNameNe : classes.val[candidateIndex.val].name ≠ queryName := by
            simpa [entryEq] using isMatch
          have recursiveEq :
              lastIndexScanReference classes.val queryName remaining
                (candidateIndex.val + 1)
                (if classes.val[candidateIndex.val]!.name = queryName
                  then candidateIndex.val else selected.val) = expected := by
            simpa [lastIndexScanReference, remainingEq] using invariant.2.2
          rw [entryBang] at recursiveEq
          simpa [nextRemaining, classNameNe] using recursiveEq
  · simp [within]
    have exhausted : classes.val.length ≤ candidateIndex.val := by
      simpa [Slice.len] using Nat.le_of_not_gt within
    have atEnd : candidateIndex.val = classes.val.length := by omega
    simpa [atEnd, lastIndexScanReference] using invariant.2.2

theorem validate_loop1_loop0_loop0_spec
    (classes : Slice NominalClass) (queryName : String)
    (selected candidateIndex : Usize)
    (hSelected : selected.val ≤ classes.val.length)
    (hCandidate : candidateIndex.val ≤ classes.val.length) :
    WP.spec
      (validate_nominal_hierarchy_loop1_loop0_loop0
        classes queryName selected candidateIndex)
      (fun output => output.val = lastIndexScanReference classes.val queryName
        (classes.val.length - candidateIndex.val) candidateIndex.val selected.val) := by
  let expected := lastIndexScanReference classes.val queryName
    (classes.val.length - candidateIndex.val) candidateIndex.val selected.val
  have initialInvariant :
      lastIndexInvariant classes queryName expected (selected, candidateIndex) :=
    ⟨hSelected, hCandidate, rfl⟩
  unfold validate_nominal_hierarchy_loop1_loop0_loop0
  apply loop.spec_decr_nat
      (measure := lastIndexRemaining classes)
      (inv := lastIndexInvariant classes queryName expected)
      (post := fun (output : Usize) => output.val = expected)
      (hInv := initialInvariant)
  intro state stateInvariant
  apply WP.spec_mono
    (validate_loop1_loop0_loop0_body_exact
      classes queryName expected state stateInvariant)
  intro flow flowPost
  cases flow <;> simpa using flowPost

theorem lastIndexScanReference_le
    (classes : List NominalClass) (queryName : String)
    (selected cursor : Nat)
    (hSelected : selected ≤ classes.length)
    (hCursor : cursor ≤ classes.length) :
    lastIndexScanReference classes queryName
        (classes.length - cursor) cursor selected ≤ classes.length := by
  induction remaining : classes.length - cursor
      generalizing cursor selected with
  | zero => simpa [lastIndexScanReference, remaining] using hSelected
  | succ tail induction =>
      have cursorWithin : cursor < classes.length := by omega
      let nextSelected :=
        if classes[cursor]!.name == queryName then cursor else selected
      have nextSelectedBound : nextSelected ≤ classes.length := by
        simp only [nextSelected]
        split <;> omega
      have nextCursorBound : cursor + 1 ≤ classes.length := by omega
      have nextRemaining : classes.length - (cursor + 1) = tail := by omega
      simpa [lastIndexScanReference, remaining, nextSelected, nextRemaining]
        using induction (cursor := cursor + 1) (selected := nextSelected)
          nextSelectedBound nextCursorBound

theorem lastIndexScanReference_lt
    (classes : List NominalClass) (queryName : String)
    (selected cursor : Nat)
    (hSelected : selected < classes.length)
    (hCursor : cursor ≤ classes.length) :
    lastIndexScanReference classes queryName
        (classes.length - cursor) cursor selected < classes.length := by
  induction remaining : classes.length - cursor
      generalizing cursor selected with
  | zero => simpa [lastIndexScanReference, remaining] using hSelected
  | succ tail induction =>
      have cursorWithin : cursor < classes.length := by omega
      let nextSelected :=
        if classes[cursor]!.name == queryName then cursor else selected
      have nextSelectedWithin : nextSelected < classes.length := by
        simp only [nextSelected]
        split <;> omega
      have nextCursorBound : cursor + 1 ≤ classes.length := by omega
      have nextRemaining : classes.length - (cursor + 1) = tail := by omega
      simpa [lastIndexScanReference, remaining, nextSelected, nextRemaining]
        using induction (cursor := cursor + 1) (selected := nextSelected)
          nextSelectedWithin nextCursorBound

theorem validate_loop1_loop0_loop0_exact
    (classes : Slice NominalClass) (queryName : String)
    (selected candidateIndex : Usize)
    (hSelected : selected.val ≤ classes.val.length)
    (hCandidate : candidateIndex.val ≤ classes.val.length) :
    validate_nominal_hierarchy_loop1_loop0_loop0
        classes queryName selected candidateIndex =
      .ok (UScalar.ofNatCore
        (lastIndexScanReference classes.val queryName
          (classes.val.length - candidateIndex.val)
          candidateIndex.val selected.val)
        (by
          have resultBound := lastIndexScanReference_le classes.val queryName
            selected.val candidateIndex.val hSelected hCandidate
          have sliceBound := classes.property
          scalar_tac)) := by
  apply result_eq_ok_of_spec_eq
  apply WP.spec_mono
    (validate_loop1_loop0_loop0_spec
      classes queryName selected candidateIndex hSelected hCandidate)
  intro output outputEq
  apply UScalar.eq_of_val_eq
  simpa using outputEq

def parentWalkFuelReference
    (classes : List NominalClass) (objectName : String) :
    Nat → Nat → Nat → Result Bool
  | 0, _, _ => .fail .integerOverflow
  | fuel + 1, current, steps =>
      if classes.length < steps then
        .ok false
      else if Usize.max ≤ steps then
        .fail .integerOverflow
      else
        match classes[current]? with
        | none => .fail .panic
        | some entry =>
            match entry.parent with
            | none => .ok true
            | some parentName =>
                if parentName == objectName then
                  .ok true
                else
                  parentWalkFuelReference classes objectName fuel
                    (lastIndexScanReference classes parentName classes.length 0 0)
                    (steps + 1)

def parentWalkReference
    (classes : List NominalClass) (objectName : String)
    (current steps : Nat) : Result Bool :=
  parentWalkFuelReference classes objectName (Usize.max - steps + 1)
    current steps

theorem validate_loop1_loop0_exact
    (classes : Slice NominalClass) (objectName : String)
    (current steps : Usize)
    (hCurrent : current.val < classes.val.length) :
    validate_nominal_hierarchy_loop1_loop0
        classes objectName true (some current) steps =
      parentWalkReference classes.val objectName current.val steps.val := by
  rw [validate_nominal_hierarchy_loop1_loop0.eq_def, loop.eq_def]
  simp only
  rw [validate_nominal_hierarchy_loop1_loop0.body.eq_def]
  by_cases overLength : steps > Slice.len classes
  · simp only [overLength, if_true]
    rw [loop.eq_def]
    simp only
    rw [validate_nominal_hierarchy_loop1_loop0.body.eq_def]
    simp only [if_false]
    have overLengthNat : classes.val.length < steps.val := by
      simpa [Slice.len] using overLength
    simp [parentWalkReference, parentWalkFuelReference, overLengthNat]
  · simp only [overLength, if_false]
    simp only [if_true]
    have withinLength : steps.val ≤ classes.val.length := by
      have notOverNat : ¬ classes.val.length < steps.val := by
        simpa [Slice.len] using overLength
      omega
    by_cases atCapacity : steps.val = Usize.max
    · have capacityScalar : steps = Usize.ofNatCore Usize.max (by scalar_tac) := by
        apply UScalar.eq_of_val_eq
        simpa using atCapacity
      rw [capacityScalar]
      have lengthCapacity : classes.val.length = Usize.max := by
        have sliceBound := classes.property
        omega
      have overflowAdd :
          Usize.ofNatCore Usize.max (by scalar_tac) + 1#usize =
            (.fail .integerOverflow : Result Usize) := by
        change UScalar.add (Usize.ofNatCore Usize.max (by scalar_tac)) 1#usize = _
        unfold UScalar.add UScalar.tryMk UScalar.tryMkOpt
        simp only [UScalar.ofNatCore_val_eq]
        rw [dif_neg]
        · rfl
        · scalar_tac
      rw [overflowAdd]
      simp [parentWalkReference, parentWalkFuelReference,
        atCapacity, lengthCapacity]
    · have belowCapacity : steps.val < Usize.max := by
        have stepsBound : steps.val ≤ Usize.max := by scalar_tac
        omega
      let nextSteps : Usize := Usize.ofNatCore (steps.val + 1) (by
        have nextBound : steps.val + 1 ≤ Usize.max := by omega
        scalar_tac)
      have nextStepsEq : nextSteps.val = steps.val + 1 := by
        simp [nextSteps]
      have addEq : (steps + 1#usize : Result Usize) = Result.ok nextSteps := by
        apply result_eq_ok_of_spec_eq
        apply WP.spec_mono (Std.Usize.add_spec (by scalar_tac))
        intro output outputEq
        apply UScalar.eq_of_val_eq
        simpa [nextSteps] using outputEq
      rw [addEq]
      let entry := classes.val[current.val]
      have entryEq : Slice.index_usize classes current = .ok entry := by
        apply result_eq_ok_of_spec_eq
        apply WP.spec_mono (Slice.index_usize_spec classes current hCurrent)
        intro output outputEq
        simpa [entry] using outputEq
      rw [entryEq]
      simp only [bind_tc_ok]
      rw [core.option.Option.Insts.CoreCloneClone.clone.eq_def]
      have notCapacityNat : ¬ Usize.max ≤ steps.val := by omega
      have entryGet : classes.val[current.val]? = some entry := by
        simp [entry, hCurrent]
      cases parentEq : entry.parent with
      | none =>
          simp only [bind_tc_ok]
          rw [loop.eq_def]
          simp only
          rw [validate_nominal_hierarchy_loop1_loop0.body.eq_def]
          simp only [if_true]
          have notOverNat : ¬ classes.val.length < steps.val := by omega
          simp [parentWalkReference, parentWalkFuelReference, notOverNat,
            notCapacityNat, entryGet, parentEq]
      | some parentName =>
          simp only [bind_tc_ok]
          rw [alloc.string.String.Insts.CoreCloneClone.clone]
          simp only [bind_tc_ok]
          have stringEq :
              alloc.string.String.Insts.CoreCmpPartialEqString.eq
                  parentName objectName = .ok (parentName == objectName) := by
            rfl
          unfold core.cmp.PartialEq.ne.trait_default
          unfold core.cmp.PartialEq.ne.default
          simp only [stringEq, bind_tc_ok]
          by_cases isObject : (parentName == objectName) = true
          · have objectEq : parentName = objectName := by simpa using isObject
            have neFalse :
                (decide ¬ (parentName == objectName) = true) = false := by
              simp [objectEq]
            simp only [neFalse, Bool.false_eq_true, if_false]
            rw [loop.eq_def]
            simp only
            rw [validate_nominal_hierarchy_loop1_loop0.body.eq_def]
            simp only [if_true]
            have notOverNat : ¬ classes.val.length < steps.val := by omega
            simp [parentWalkReference, parentWalkFuelReference, notOverNat,
              notCapacityNat, entryGet, parentEq, objectEq]
          · have notObject : (parentName == objectName) = false :=
              Bool.eq_false_of_not_eq_true isObject
            have neTrue :
                (decide ¬ (parentName == objectName) = true) = true := by
              simp [notObject]
            simp only [neTrue, if_true]
            rw [validate_loop1_loop0_loop0_exact classes parentName 0#usize 0#usize
              (by simp) (by simp)]
            simp only [bind_tc_ok]
            rw [← validate_nominal_hierarchy_loop1_loop0.eq_def]
            rw [validate_loop1_loop0_exact]
            have notOverNat : ¬ classes.val.length < steps.val := by omega
            conv_rhs =>
              rw [parentWalkReference, parentWalkFuelReference]
              simp only [notOverNat, notCapacityNat, entryGet, parentEq,
                notObject, if_false]
            rw [parentWalkReference, nextStepsEq]
            have fuelEq :
                Usize.max - (steps.val + 1) + 1 = Usize.max - steps.val := by
              omega
            rw [fuelEq]
            simp only [UScalar.ofNatCore_val_eq, notObject,
              Bool.false_eq_true, if_false, Nat.sub_zero]
            apply lastIndexScanReference_lt classes.val parentName 0 0
            · omega
            · omega
termination_by Usize.max - steps.val + 1
decreasing_by
  simp_wf
  omega

def phaseTwoScanReference
    (classes : List NominalClass) (objectName : String) :
    Nat → Nat → Bool → Result Bool
  | 0, _, valid => .ok valid
  | remaining + 1, index, valid =>
      if valid then do
        let nextValid ← parentWalkReference classes objectName index 0
        phaseTwoScanReference classes objectName remaining (index + 1) nextValid
      else
        phaseTwoScanReference classes objectName remaining (index + 1) false

theorem validate_loop1_exact
    (classes : Slice NominalClass) (objectName : String)
    (valid : Bool) (index : Usize)
    (hIndex : index.val ≤ classes.val.length) :
    validate_nominal_hierarchy_loop1 classes objectName valid index =
      phaseTwoScanReference classes.val objectName
        (classes.val.length - index.val) index.val valid := by
  induction remaining : classes.val.length - index.val
      generalizing index valid with
  | zero =>
      rw [validate_nominal_hierarchy_loop1.eq_def, loop.eq_def]
      simp only
      rw [validate_nominal_hierarchy_loop1.body.eq_def]
      have exhausted : ¬ index < Slice.len classes := by
        simpa [Slice.len] using (show ¬ index.val < classes.val.length by omega)
      simp [exhausted, phaseTwoScanReference, remaining]
  | succ tail induction =>
      have indexWithinNat : index.val < classes.val.length := by omega
      have indexWithin : index < Slice.len classes := by
        simpa [Slice.len] using indexWithinNat
      have nextIndexCapacity : index.val + 1 ≤ Usize.max := by
        have sliceBound := classes.property
        omega
      let nextIndex : Usize := Usize.ofNatCore (index.val + 1) (by
        scalar_tac)
      have nextIndexEq : nextIndex.val = index.val + 1 := by
        simp [nextIndex]
      have nextIndexBound : nextIndex.val ≤ classes.val.length := by omega
      have addEq : (index + 1#usize : Result Usize) = .ok nextIndex := by
        apply result_eq_ok_of_spec_eq
        apply WP.spec_mono (Std.Usize.add_spec (by scalar_tac))
        intro output outputEq
        apply UScalar.eq_of_val_eq
        simpa [nextIndex] using outputEq
      rw [validate_nominal_hierarchy_loop1.eq_def, loop.eq_def]
      simp only
      rw [validate_nominal_hierarchy_loop1.body.eq_def]
      simp only [indexWithin, if_true]
      by_cases stillValid : valid = true
      · simp only [stillValid, if_true]
        rw [validate_loop1_loop0_exact classes objectName index 0#usize indexWithinNat]
        cases walkResult : parentWalkReference classes.val objectName index.val 0 with
        | fail error =>
            have walkResult' :
                parentWalkReference classes.val objectName index.val
                    (0#usize).val = .fail error := by
              exact walkResult
            conv_rhs =>
              rw [phaseTwoScanReference]
              simp only [stillValid, if_true, walkResult, bind_tc_fail]
            rw [walkResult']
            rw [bind_tc_fail]
        | div =>
            have walkResult' :
                parentWalkReference classes.val objectName index.val
                    (0#usize).val = .div := by
              exact walkResult
            conv_rhs =>
              rw [phaseTwoScanReference]
              simp only [stillValid, if_true, walkResult, bind_tc_div]
            rw [walkResult']
            rw [bind_tc_div]
        | ok nextValid =>
            have walkResult' :
                parentWalkReference classes.val objectName index.val
                    (0#usize).val = .ok nextValid := by
              exact walkResult
            rw [walkResult', addEq]
            rw [bind_tc_ok, bind_tc_ok]
            change validate_nominal_hierarchy_loop1 classes objectName
                nextValid nextIndex = _
            have nextRemaining :
                classes.val.length - nextIndex.val = tail := by omega
            rw [induction (index := nextIndex) (valid := nextValid)
              nextIndexBound nextRemaining]
            conv_rhs =>
              rw [phaseTwoScanReference]
              simp only [stillValid, if_true, walkResult, bind_tc_ok]
            rw [nextIndexEq]
      · have invalid : valid = false := Bool.eq_false_of_not_eq_true stillValid
        simp only [invalid, Bool.false_eq_true, if_false]
        rw [addEq]
        simp only [bind_tc_ok]
        rw [← validate_nominal_hierarchy_loop1.eq_def]
        have nextRemaining :
            classes.val.length - nextIndex.val = tail := by omega
        rw [induction (index := nextIndex) (valid := false) nextIndexBound
          nextRemaining]
        conv_rhs =>
          rw [phaseTwoScanReference]
          simp only [invalid, Bool.false_eq_true, if_false]
        rw [nextIndexEq]

def validateNominalHierarchyResultReference
    (classes : List NominalClass) : Result Bool :=
  let objectName := "object"
  let phaseOne := phaseOneScanReference classes objectName classes.length 0 true
  if phaseOne then
    phaseTwoScanReference classes objectName classes.length 0 true
  else
    .ok false

theorem object_name_from_str_exact :
    alloc.string.String.Insts.CoreConvertFromShared0Str.from (toStr "object") =
      .ok "object" := by
  unfold alloc.string.String.Insts.CoreConvertFromShared0Str.from
  let objectBytes := ByteArray.mk <|
    ((toStr "object").val.map (fun byte => UInt8.ofBitVec byte.bv)).toArray
  change (match String.fromUTF8? objectBytes with
    | some string => Result.ok string
    | none => Result.fail Error.panic) = Result.ok "object"
  rw [show String.fromUTF8? objectBytes = some "object" by native_decide]

theorem validate_nominal_hierarchy_all_inputs_exact
    (classes : Slice NominalClass) :
    validate_nominal_hierarchy classes =
      validateNominalHierarchyResultReference classes.val := by
  rw [validate_nominal_hierarchy, object_name_from_str_exact, bind_tc_ok]
  rw [validate_loop0_exact classes "object" true 0#usize (by simp)]
  rw [bind_tc_ok]
  change
    (if phaseOneScanReference classes.val "object" classes.val.length 0 true = true
      then validate_nominal_hierarchy_loop1 classes "object" true 0#usize
      else .ok false) =
    (if phaseOneScanReference classes.val "object" classes.val.length 0 true = true
      then phaseTwoScanReference classes.val "object" classes.val.length 0 true
      else .ok false)
  by_cases phaseOneValid :
      phaseOneScanReference classes.val "object" classes.val.length 0 true = true
  · rw [phaseOneValid]
    rw [validate_loop1_exact classes "object" true 0#usize (by simp)]
    rfl
  · have phaseOneInvalid :
        phaseOneScanReference classes.val "object" classes.val.length 0 true =
          false := Bool.eq_false_of_not_eq_true phaseOneValid
    rw [phaseOneInvalid]
    rfl

def buildNominalHierarchyResultReference
    (classes : List NominalClass) : Result (Option NominalHierarchy) :=
  match validateNominalHierarchyResultReference classes with
  | .fail error => .fail error
  | .div => .div
  | .ok false => .ok none
  | .ok true =>
      .ok (some { classes := prependNominalClasses classes .Empty })

theorem build_nominal_hierarchy_all_inputs_exact
    (classes : alloc.vec.Vec NominalClass) :
    build_nominal_hierarchy classes =
      buildNominalHierarchyResultReference classes.val := by
  rw [build_nominal_hierarchy]
  rw [validate_nominal_hierarchy_all_inputs_exact
    (alloc.vec.Vec.deref classes)]
  change
    (do
      let valid ← validateNominalHierarchyResultReference classes.val
      if valid = true then
        let classList ← NominalClassList.from_vec classes
        Result.ok (some { classes := classList })
      else
        Result.ok none) = buildNominalHierarchyResultReference classes.val
  cases validationResult : validateNominalHierarchyResultReference classes.val with
  | fail error =>
      simp [validationResult, buildNominalHierarchyResultReference]
  | div =>
      simp [validationResult, buildNominalHierarchyResultReference]
  | ok valid =>
      cases valid
      · simp [validationResult, buildNominalHierarchyResultReference]
      · simp only [validationResult, bind_tc_ok, if_true]
        rw [nominalClassList_from_vec_exact_hierarchy]
        rw [bind_tc_ok]
        rw [buildNominalHierarchyResultReference, validationResult]

end NominalConstruction

end TypeAlgebraKernel.Proofs
