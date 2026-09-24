import Maledictus.ModuleHeapOperators

namespace Maledictus

/-!
# Homogeneous single-generator collection comprehensions

This module gives a constructive model for the v58 comprehension tranche.  A source is an
abstract finite homogeneous list.  Mapping and filtering are pure functions, so the recursive
definitions record Python's left-to-right source order without modeling expression evaluation
events.  Lists retain production order, sets insert unique mapped values in production order, and
dict lookup is a left fold whose later writes replace earlier values for the same integer key.

The frontend correspondence is deliberately outside these theorem claims.  In particular, the
Rust frontend must separately prove that an AST has one direct synchronous generator, a builtin
homogeneous list source, a direct local target, total effect-free mapping/filter expressions, and
the expected result sorts.  These theorems do not validate AST syntax, infer `Term` sorts, prove
purity, authorize custom iteration, or justify Python bool/int key equivalence.  The accepted dict
model has homogeneous integer keys only.
-/

structure ComprehensionShape where
  generatorCount : Nat
  filterCount : Nat
  asynchronous : Bool
  nestedComprehension : Bool
  sourceEffectFree : Bool
  bodyEffectFree : Bool
  filtersEffectFree : Bool
  builtinHomogeneousListSource : Bool
  directLocalTarget : Bool

inductive ComprehensionKind where
  | list
  | dictWithIntegerKeys
  | set
  deriving DecidableEq

structure AuthorizedComprehension where
  kind : ComprehensionKind
  shape : ComprehensionShape

def authorizeComprehension
    (kind : ComprehensionKind) (shape : ComprehensionShape) :
    Option AuthorizedComprehension :=
  if shape.generatorCount != 1 then none
  else if 1 < shape.filterCount then none
  else if shape.asynchronous then none
  else if shape.nestedComprehension then none
  else if !shape.sourceEffectFree then none
  else if !shape.bodyEffectFree then none
  else if !shape.filtersEffectFree then none
  else if !shape.builtinHomogeneousListSource then none
  else if !shape.directLocalTarget then none
  else some { kind, shape }

theorem supported_single_generator_comprehension_authorizes
    (kind : ComprehensionKind) (shape : ComprehensionShape)
    (single : shape.generatorCount = 1)
    (filterBound : shape.filterCount ≤ 1)
    (synchronous : shape.asynchronous = false)
    (notNested : shape.nestedComprehension = false)
    (sourcePure : shape.sourceEffectFree = true)
    (bodyPure : shape.bodyEffectFree = true)
    (filtersPure : shape.filtersEffectFree = true)
    (builtinSource : shape.builtinHomogeneousListSource = true)
    (directTarget : shape.directLocalTarget = true) :
    authorizeComprehension kind shape = some { kind, shape } := by
  have notMultipleFilters : ¬1 < shape.filterCount := Nat.not_lt.mpr filterBound
  simp [authorizeComprehension, single, notMultipleFilters, synchronous, notNested, sourcePure,
    bodyPure, filtersPure, builtinSource, directTarget]

theorem multiple_generator_comprehension_refuses
    (kind : ComprehensionKind) (shape : ComprehensionShape)
    (multiple : shape.generatorCount ≠ 1) :
    authorizeComprehension kind shape = none := by
  simp [authorizeComprehension, multiple]

theorem multiple_filter_comprehension_refuses
    (kind : ComprehensionKind) (shape : ComprehensionShape)
    (multipleFilters : 1 < shape.filterCount) :
    authorizeComprehension kind shape = none := by
  simp [authorizeComprehension, multipleFilters]

theorem asynchronous_comprehension_refuses
    (kind : ComprehensionKind) (shape : ComprehensionShape)
    (asynchronous : shape.asynchronous = true) :
    authorizeComprehension kind shape = none := by
  simp [authorizeComprehension, asynchronous]

theorem nested_comprehension_refuses
    (kind : ComprehensionKind) (shape : ComprehensionShape)
    (nested : shape.nestedComprehension = true) :
    authorizeComprehension kind shape = none := by
  simp [authorizeComprehension, nested]

theorem effectful_source_comprehension_refuses
    (kind : ComprehensionKind) (shape : ComprehensionShape)
    (effectful : shape.sourceEffectFree = false) :
    authorizeComprehension kind shape = none := by
  simp [authorizeComprehension, effectful]

theorem effectful_body_comprehension_refuses
    (kind : ComprehensionKind) (shape : ComprehensionShape)
    (effectful : shape.bodyEffectFree = false) :
    authorizeComprehension kind shape = none := by
  simp [authorizeComprehension, effectful]

theorem effectful_filter_comprehension_refuses
    (kind : ComprehensionKind) (shape : ComprehensionShape)
    (effectful : shape.filtersEffectFree = false) :
    authorizeComprehension kind shape = none := by
  simp [authorizeComprehension, effectful]

theorem custom_iteration_comprehension_refuses
    (kind : ComprehensionKind) (shape : ComprehensionShape)
    (custom : shape.builtinHomogeneousListSource = false) :
    authorizeComprehension kind shape = none := by
  simp [authorizeComprehension, custom]

theorem nested_target_comprehension_refuses
    (kind : ComprehensionKind) (shape : ComprehensionShape)
    (nestedTarget : shape.directLocalTarget = false) :
    authorizeComprehension kind shape = none := by
  simp [authorizeComprehension, nestedTarget]

/-! Ordered list mapping and filtering. -/

def orderedFilterMap (mapValue : α → β) (passes : α → Bool) : List α → List β
  | [] => []
  | value :: rest =>
      if passes value then mapValue value :: orderedFilterMap mapValue passes rest
      else orderedFilterMap mapValue passes rest

theorem ordered_filter_map_pass_cons
    (mapValue : α → β) (passes : α → Bool) (value : α) (rest : List α)
    (accepted : passes value = true) :
    orderedFilterMap mapValue passes (value :: rest) =
      mapValue value :: orderedFilterMap mapValue passes rest := by
  simp [orderedFilterMap, accepted]

theorem ordered_filter_map_fail_skips
    (mapValue : α → β) (passes : α → Bool) (value : α) (rest : List α)
    (rejected : passes value = false) :
    orderedFilterMap mapValue passes (value :: rest) =
      orderedFilterMap mapValue passes rest := by
  simp [orderedFilterMap, rejected]

theorem ordered_filter_map_membership_witness
    (mapValue : α → β) (passes : α → Bool) (source : List α) (resultValue : β) :
    resultValue ∈ orderedFilterMap mapValue passes source ↔
      ∃ sourceValue, sourceValue ∈ source ∧ passes sourceValue = true ∧
        mapValue sourceValue = resultValue := by
  induction source with
  | nil => simp [orderedFilterMap]
  | cons head tail inductionHypothesis =>
      cases accepted : passes head
      · simp [orderedFilterMap, accepted, inductionHypothesis]
      · constructor
        · intro member
          simp only [orderedFilterMap, accepted, ↓reduceIte, List.mem_cons] at member
          rcases member with same | tailMember
          · exact ⟨head, by simp, accepted, same.symm⟩
          · rcases inductionHypothesis.mp tailMember with
              ⟨sourceValue, sourceMember, sourceAccepted, mapped⟩
            exact ⟨sourceValue, by simp [sourceMember], sourceAccepted, mapped⟩
        · rintro ⟨sourceValue, sourceMember, sourceAccepted, mapped⟩
          simp only [orderedFilterMap, accepted, ↓reduceIte, List.mem_cons]
          simp only [List.mem_cons] at sourceMember
          rcases sourceMember with same | tailMember
          · subst sourceValue
            exact Or.inl mapped.symm
          · exact Or.inr (inductionHypothesis.mpr
              ⟨sourceValue, tailMember, sourceAccepted, mapped⟩)

theorem passing_source_value_produces_list_member
    (mapValue : α → β) (passes : α → Bool) (source : List α) (sourceValue : α)
    (member : sourceValue ∈ source) (accepted : passes sourceValue = true) :
    mapValue sourceValue ∈ orderedFilterMap mapValue passes source := by
  exact (ordered_filter_map_membership_witness mapValue passes source
    (mapValue sourceValue)).mpr ⟨sourceValue, member, accepted, rfl⟩

theorem ordered_filter_map_length_upper_bound
    (mapValue : α → β) (passes : α → Bool) (source : List α) :
    (orderedFilterMap mapValue passes source).length ≤ source.length := by
  induction source with
  | nil => simp [orderedFilterMap]
  | cons head tail inductionHypothesis =>
      cases accepted : passes head
      · simp only [orderedFilterMap, accepted, Bool.false_eq_true, ↓reduceIte,
          List.length_cons]
        omega
      · simp [orderedFilterMap, accepted, inductionHypothesis]

theorem ordered_unfiltered_map_is_list_map
    (mapValue : α → β) (source : List α) :
    orderedFilterMap mapValue (fun _ => true) source = source.map mapValue := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [orderedFilterMap, inductionHypothesis]

theorem ordered_unfiltered_map_preserves_length
    (mapValue : α → β) (source : List α) :
    (orderedFilterMap mapValue (fun _ => true) source).length = source.length := by
  rw [ordered_unfiltered_map_is_list_map]
  simp

/-! Unique set insertion.  The list representation exposes deterministic construction order only;
the public semantic facts below concern membership and cardinality. -/

def appendUnique [DecidableEq α] (values : List α) (value : α) : List α :=
  if value ∈ values then values else values ++ [value]

def orderedUnique [DecidableEq α] (values : List α) : List α :=
  values.foldl appendUnique []

def orderedSetComprehension [DecidableEq β]
    (mapValue : α → β) (passes : α → Bool) (source : List α) : List β :=
  orderedUnique (orderedFilterMap mapValue passes source)

theorem append_unique_membership [DecidableEq α]
    (values : List α) (inserted candidate : α) :
    candidate ∈ appendUnique values inserted ↔ candidate ∈ values ∨ candidate = inserted := by
  by_cases present : inserted ∈ values
  · simp [appendUnique, present]
    intro same
    subst candidate
    exact present
  · simp [appendUnique, present]

theorem ordered_unique_fold_membership [DecidableEq α]
    (source accumulator : List α) (candidate : α) :
    candidate ∈ source.foldl appendUnique accumulator ↔
      candidate ∈ accumulator ∨ candidate ∈ source := by
  induction source generalizing accumulator with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      rw [append_unique_membership]
      simp only [List.mem_cons]
      exact or_assoc

theorem ordered_unique_membership [DecidableEq α]
    (source : List α) (candidate : α) :
    candidate ∈ orderedUnique source ↔ candidate ∈ source := by
  simp [orderedUnique, ordered_unique_fold_membership]

theorem ordered_set_comprehension_membership_witness [DecidableEq β]
    (mapValue : α → β) (passes : α → Bool) (source : List α) (candidate : β) :
    candidate ∈ orderedSetComprehension mapValue passes source ↔
      ∃ sourceValue, sourceValue ∈ source ∧ passes sourceValue = true ∧
        mapValue sourceValue = candidate := by
  rw [orderedSetComprehension, ordered_unique_membership]
  exact ordered_filter_map_membership_witness mapValue passes source candidate

theorem append_unique_length_le_successor [DecidableEq α]
    (values : List α) (value : α) :
    (appendUnique values value).length ≤ values.length + 1 := by
  by_cases present : value ∈ values <;> simp [appendUnique, present]

theorem append_unique_preserves_nodup [DecidableEq α]
    (values : List α) (value : α) (unique : values.Nodup) :
    (appendUnique values value).Nodup := by
  by_cases present : value ∈ values
  · simpa [appendUnique, present] using unique
  · rw [appendUnique, if_neg present, List.nodup_append]
    constructor
    · exact unique
    constructor
    · simp
    · intro candidate inValues inSingleton inSingletonMember
      have singletonValue : inSingleton = value := by simpa using inSingletonMember
      subst inSingleton
      intro same
      subst candidate
      exact present inValues

theorem ordered_unique_is_nodup [DecidableEq α] (source : List α) :
    (orderedUnique source).Nodup := by
  unfold orderedUnique
  have generalized : ∀ accumulator : List α, accumulator.Nodup →
      (source.foldl appendUnique accumulator).Nodup := by
    induction source with
    | nil => simp
    | cons head tail inductionHypothesis =>
        intro accumulator unique
        rw [List.foldl_cons]
        exact inductionHypothesis (appendUnique accumulator head)
          (append_unique_preserves_nodup accumulator head unique)
  exact generalized [] (by simp)

theorem ordered_unique_fold_length_bound [DecidableEq α]
    (source accumulator : List α) :
    (source.foldl appendUnique accumulator).length ≤ accumulator.length + source.length := by
  induction source generalizing accumulator with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons]
      have recursive := inductionHypothesis (appendUnique accumulator head)
      have inserted := append_unique_length_le_successor accumulator head
      simp only [List.length_cons]
      omega

theorem ordered_unique_length_upper_bound [DecidableEq α] (source : List α) :
    (orderedUnique source).length ≤ source.length := by
  simpa [orderedUnique] using ordered_unique_fold_length_bound source ([] : List α)

theorem ordered_set_comprehension_length_upper_bound [DecidableEq β]
    (mapValue : α → β) (passes : α → Bool) (source : List α) :
    (orderedSetComprehension mapValue passes source).length ≤ source.length := by
  exact Nat.le_trans (ordered_unique_length_upper_bound
    (orderedFilterMap mapValue passes source))
    (ordered_filter_map_length_upper_bound mapValue passes source)

/-! Integer-key dict lookup with Python's last-write-wins rule. -/

def dictComprehensionWrite
    (key : Int) (value : β) (query : Int) (current : Option β) : Option β :=
  if key == query then some value else current

def dictComprehensionLookup
    (keyOf : α → Int) (valueOf : α → β) (passes : α → Bool)
    (source : List α) (query : Int) : Option β :=
  source.foldl (fun current sourceValue =>
    if passes sourceValue then
      dictComprehensionWrite (keyOf sourceValue) (valueOf sourceValue) query current
    else current) none

def dictComprehensionKeys
    (keyOf : α → Int) (passes : α → Bool) (source : List α) : List Int :=
  orderedSetComprehension keyOf passes source

theorem dict_comprehension_key_list_membership_witness
    (keyOf : α → Int) (passes : α → Bool) (source : List α) (query : Int) :
    query ∈ dictComprehensionKeys keyOf passes source ↔
      ∃ sourceValue, sourceValue ∈ source ∧ passes sourceValue = true ∧
        keyOf sourceValue = query := by
  exact ordered_set_comprehension_membership_witness keyOf passes source query

theorem dict_comprehension_length_upper_bound
    (keyOf : α → Int) (passes : α → Bool) (source : List α) :
    (dictComprehensionKeys keyOf passes source).length ≤ source.length := by
  exact ordered_set_comprehension_length_upper_bound keyOf passes source

theorem dict_lookup_fold_key_membership_witness
    (keyOf : α → Int) (valueOf : α → β) (passes : α → Bool)
    (source : List α) (query : Int) (current : Option β) :
    (source.foldl (fun current sourceValue =>
      if passes sourceValue then
        dictComprehensionWrite (keyOf sourceValue) (valueOf sourceValue) query current
      else current) current).isSome = true ↔
      current.isSome = true ∨
        ∃ sourceValue, sourceValue ∈ source ∧ passes sourceValue = true ∧
          keyOf sourceValue = query := by
  induction source generalizing current with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      cases accepted : passes head
      · simp [accepted]
      · by_cases keyMatches : keyOf head = query
        · simp [accepted, dictComprehensionWrite, keyMatches]
        · simp [accepted, dictComprehensionWrite, keyMatches]

theorem dict_comprehension_key_membership_witness
    (keyOf : α → Int) (valueOf : α → β) (passes : α → Bool)
    (source : List α) (query : Int) :
    (dictComprehensionLookup keyOf valueOf passes source query).isSome = true ↔
      ∃ sourceValue, sourceValue ∈ source ∧ passes sourceValue = true ∧
        keyOf sourceValue = query := by
  simpa [dictComprehensionLookup] using
    (dict_lookup_fold_key_membership_witness keyOf valueOf passes source query
      (none : Option β))

theorem dict_comprehension_last_source_write_wins
    (keyOf : α → Int) (valueOf : α → β) (passes : α → Bool)
    (priorValues : List α) (last : α)
    (accepted : passes last = true) :
    dictComprehensionLookup keyOf valueOf passes (priorValues ++ [last]) (keyOf last) =
      some (valueOf last) := by
  simp [dictComprehensionLookup, List.foldl_append, accepted,
    dictComprehensionWrite]

theorem dict_comprehension_rejected_last_does_not_write
    (keyOf : α → Int) (valueOf : α → β) (passes : α → Bool)
    (priorValues : List α) (last : α) (query : Int)
    (rejected : passes last = false) :
    dictComprehensionLookup keyOf valueOf passes (priorValues ++ [last]) query =
      dictComprehensionLookup keyOf valueOf passes priorValues query := by
  simp [dictComprehensionLookup, List.foldl_append, rejected]

theorem dict_comprehension_later_duplicate_overwrites
    (keyOf : α → Int) (valueOf : α → β) (passes : α → Bool)
    (priorValues : List α) (earlier later : α)
    (laterAccepted : passes later = true)
    (duplicate : keyOf earlier = keyOf later) :
    dictComprehensionLookup keyOf valueOf passes
      (priorValues ++ [earlier, later]) (keyOf earlier) = some (valueOf later) := by
  rw [duplicate]
  simpa [List.append_assoc] using
    (dict_comprehension_last_source_write_wins keyOf valueOf passes
      (priorValues ++ [earlier]) later laterAccepted)

inductive ComprehensionKeySort where
  | integer
  | boolean
  deriving DecidableEq

def integerDictKeySortAccepted : ComprehensionKeySort → Bool
  | .integer => true
  | .boolean => false

theorem bool_dict_key_normalization_is_not_claimed :
    integerDictKeySortAccepted .boolean = false := by
  rfl

end Maledictus
