namespace Maledictus

inductive ValueSort where
  | bool
  | int
  | string
  | unit
  | reference
  | class
  | bytes
  | range
  | tuple : List ValueSort → ValueSort
  | list : ValueSort → ValueSort

mutual

def valueSortBeq : ValueSort → ValueSort → Bool
  | .bool, .bool => true
  | .int, .int => true
  | .string, .string => true
  | .unit, .unit => true
  | .reference, .reference => true
  | .class, .class => true
  | .bytes, .bytes => true
  | .range, .range => true
  | .tuple left, .tuple right => valueSortListBeq left right
  | .list left, .list right => valueSortBeq left right
  | _, _ => false

def valueSortListBeq : List ValueSort → List ValueSort → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      valueSortBeq left right && valueSortListBeq leftRest rightRest
  | _, _ => false

end

instance instBEqValueSort : BEq ValueSort := ⟨valueSortBeq⟩

/-- Expose the custom recursive equality through `BEq.beq`. Lean's
    simplifier does not unfold a typeclass projection merely because the
    instance constructor and its function are listed separately. -/
@[simp] theorem valueSort_beq_eq_valueSortBeq (left right : ValueSort) :
    (left == right) = valueSortBeq left right := by
  rfl

inductive RangeConstructionOutcome where
  | returned : List Int → RangeConstructionOutcome
  | raisedValueError : RangeConstructionOutcome
  deriving DecidableEq

def literalRangeOutcome (step : Int) (values : List Int) : RangeConstructionOutcome :=
  if step = 0 then .raisedValueError else .returned values

theorem literalRangeOutcome_zero (values : List Int) :
    literalRangeOutcome 0 values = .raisedValueError := by
  simp [literalRangeOutcome]

theorem literalRangeOutcome_nonzero (step : Int) (values : List Int) (step_ne_zero : step ≠ 0) :
    literalRangeOutcome step values = .returned values := by
  simp [literalRangeOutcome, step_ne_zero]

inductive Term where
  | boolLiteral : Bool → Term
  | intLiteral : Int → Term
  | stringLiteral : String → Term
  | bytesLiteral : List Nat → Term
  | rangeLiteral : List Int → Term
  | unitLiteral : Term
  | nullReference : Term
  | nominalReference : String → String → Term
  | classLiteral : String → Term
  | runtimeClass : Term → Term
  | predicateInstance : String → List Term → Term
  | classSubtype : Term → Term → Term
  | variable : String → ValueSort → Term
  | fieldRead : Nat → Term → String → ValueSort → Term
  | permissionAtLeast : Nat → Term → String → Nat → Nat → Term
  | permissionAtMost : Nat → Term → String → Nat → Nat → Term
  | permissionPositive : Nat → Term → String → Term
  | permissionMaskValid : Nat → String → Term
  | permissionMaskTransition :
      Nat → Nat → String → List (Term × Nat × Nat) → List (Term × Nat × Nat) → Term
  | not : Term → Term
  | and : List Term → Term
  | or : List Term → Term
  | implies : Term → Term → Term
  | ite : Term → Term → Term → Term
  | equal : Term → Term → Term
  | less : Term → Term → Term
  | lessEqual : Term → Term → Term
  | greater : Term → Term → Term
  | greaterEqual : Term → Term → Term
  | add : Term → Term → Term
  | subtract : Term → Term → Term
  | multiply : Term → Term → Term
  | floorDivideByPositive : Term → Nat → Term
  | negate : Term → Term
  | stringConcat : List Term → Term
  | stringLength : Term → Term
  | bytesConcat : List Term → Term
  | bytesLength : Term → Term
  | bytesGet : Term → Term → Term
  | tuple : List Term → Term
  | tupleGet : Term → Nat → Term
  | list : ValueSort → List Term → Term
  | listLength : Term → Term
  | listGet : Term → Term → Term

def isHeapFieldSort : ValueSort → Bool
  | .unit => false
  | .class => false
  | .tuple _ => false
  | .list _ => false
  | .bytes => false
  | .range => false
  | _ => true

def isListElementSort : ValueSort → Bool
  | .bool | .int | .string | .reference | .bytes => true
  | _ => false

mutual

def inferSort : Term → Option ValueSort
    | .boolLiteral _ => some .bool
    | .intLiteral _ => some .int
    | .stringLiteral _ => some .string
    | .bytesLiteral _ => some .bytes
    | .rangeLiteral _ => some .range
    | .unitLiteral => some .unit
    | .nullReference => some .reference
    | .nominalReference _ className => if className.isEmpty then none else some .reference
    | .classLiteral className => if className.isEmpty then none else some .class
    | .runtimeClass value =>
        if inferSort value == some .reference then some .class else none
    | .predicateInstance predicate arguments =>
        if !predicate.isEmpty && !arguments.isEmpty && allPredicateArguments arguments
        then some .reference else none
    | .classSubtype actual expected =>
        if inferSort actual == some .class && inferSort expected == some .class
        then some .bool else none
    | .variable _ sort => some sort
    | .fieldRead _ receiver _ sort =>
        if inferSort receiver == some .reference && isHeapFieldSort sort then some sort else none
    | .permissionAtLeast _ receiver _ numerator denominator =>
        if inferSort receiver == some .reference && denominator != 0 && numerator <= denominator
        then some .bool else none
    | .permissionAtMost _ receiver _ numerator denominator =>
        if inferSort receiver == some .reference && denominator != 0 && numerator <= denominator
        then some .bool else none
    | .permissionPositive _ receiver _ =>
        if inferSort receiver == some .reference then some .bool else none
    | .permissionMaskValid _ field =>
        if field.isEmpty then none else some .bool
    | .permissionMaskTransition preMask postMask field consumed produced =>
        if preMask != postMask && !field.isEmpty &&
            allPermissionTransferAmounts consumed && allPermissionTransferAmounts produced
        then some .bool else none
    | .not value => if inferSort value == some .bool then some .bool else none
    | .and values =>
        if allBool values then some .bool else none
    | .or values =>
        if allBool values then some .bool else none
    | .implies left right =>
        if inferSort left == some .bool && inferSort right == some .bool then some .bool else none
    | .ite condition thenValue elseValue =>
        if inferSort condition == some .bool then
          match inferSort thenValue, inferSort elseValue with
          | some thenSort, some elseSort => if thenSort == elseSort then some thenSort else none
          | _, _ => none
        else none
    | .equal left right =>
        match inferSort left, inferSort right with
        | some leftSort, some rightSort => if leftSort == rightSort then some .bool else none
        | _, _ => none
    | .less left right =>
        if inferSort left == some .int && inferSort right == some .int then some .bool else none
    | .lessEqual left right =>
        if inferSort left == some .int && inferSort right == some .int then some .bool else none
    | .greater left right =>
        if inferSort left == some .int && inferSort right == some .int then some .bool else none
    | .greaterEqual left right =>
        if inferSort left == some .int && inferSort right == some .int then some .bool else none
    | .add left right =>
        if inferSort left == some .int && inferSort right == some .int then some .int else none
    | .subtract left right =>
        if inferSort left == some .int && inferSort right == some .int then some .int else none
    | .multiply left right =>
        if inferSort left == some .int && inferSort right == some .int then some .int else none
    | .floorDivideByPositive value divisor =>
        if inferSort value == some .int && divisor != 0 then some .int else none
    | .negate value => if inferSort value == some .int then some .int else none
    | .stringConcat values => if allString values then some .string else none
    | .stringLength value => if inferSort value == some .string then some .int else none
    | .bytesConcat values => if allBytes values then some .bytes else none
    | .bytesLength value => if inferSort value == some .bytes then some .int else none
    | .bytesGet value index =>
        if inferSort value == some .bytes && inferSort index == some .int then some .int else none
    | .tuple values => Option.map .tuple (inferTupleSorts values)
    | .tupleGet value index =>
        match inferSort value with
        | some (.tuple sorts) => sorts[index]?
        | _ => none
    | .list elementSort values =>
        if isListElementSort elementSort && allOfSort values elementSort
        then some (.list elementSort) else none
    | .listLength value =>
        match inferSort value with
        | some (.list _) => some .int
        | _ => none
    | .listGet value index =>
        match inferSort value with
        | some (.list elementSort) =>
            if inferSort index == some .int then some elementSort else none
        | _ => none

def allBool : List Term → Bool
    | [] => true
    | value :: rest => inferSort value == some .bool && allBool rest

def allString : List Term → Bool
    | [] => true
    | value :: rest => inferSort value == some .string && allString rest

def allBytes : List Term → Bool
    | [] => true
    | value :: rest => inferSort value == some .bytes && allBytes rest

def allPredicateArguments : List Term → Bool
    | [] => true
    | value :: rest =>
        match inferSort value with
        | some .bool | some .int | some .string | some .reference | some .class =>
            allPredicateArguments rest
        | _ => false

def inferTupleSorts : List Term → Option (List ValueSort)
    | [] => some []
    | value :: rest =>
        match inferSort value, inferTupleSorts rest with
        | some sort, some sorts => some (sort :: sorts)
        | _, _ => none

def allOfSort : List Term → ValueSort → Bool
    | [], _ => true
    | value :: rest, sort => inferSort value == some sort && allOfSort rest sort

def allPermissionTransferAmounts : List (Term × Nat × Nat) → Bool
    | [] => true
    | (receiver, numerator, denominator) :: rest =>
        inferSort receiver == some .reference && denominator != 0 && numerator <= denominator &&
          allPermissionTransferAmounts rest

end

theorem predicate_instance_name_and_arguments_injective
    {leftName rightName : String} {leftArguments rightArguments : List Term}
    (equalInstances :
      Term.predicateInstance leftName leftArguments =
        Term.predicateInstance rightName rightArguments) :
    leftName = rightName ∧ leftArguments = rightArguments := by
  injection equalInstances with nameEquality argumentEquality
  exact ⟨nameEquality, argumentEquality⟩

def integerAbsTerm (value : Term) : Term :=
  .ite (.less value (.intLiteral 0)) (.negate value) value

def integerMinTerm (left right : Term) : Term :=
  .ite (.lessEqual left right) left right

def integerMaxTerm (left right : Term) : Term :=
  .ite (.greaterEqual left right) left right

def nonnegativeIntegerPowerTerm (base : Term) : Nat → Term
  | 0 => .intLiteral 1
  | exponent + 1 => .multiply (nonnegativeIntegerPowerTerm base exponent) base

def dynamicTupleSelectTerm (index fallback : Term) : List (Nat × Term) → Term
  | [] => fallback
  | (position, value) :: rest =>
      .ite (.equal index (.intLiteral position)) value
        (dynamicTupleSelectTerm index fallback rest)

def allIndexedOfSort : List (Nat × Term) → ValueSort → Prop
  | [], _ => True
  | (_, value) :: rest, sort =>
      inferSort value = some sort ∧ allIndexedOfSort rest sort

abbrev ModuleEnvironment := List (String × Term)

def moduleLookup : ModuleEnvironment → String → Option Term
  | [], _ => none
  | (boundName, value) :: rest, name =>
      if name = boundName then some value else moduleLookup rest name

def moduleContains : ModuleEnvironment → String → Bool
  | [], _ => false
  | (boundName, _) :: rest, name =>
      if name = boundName then true else moduleContains rest name

def insertImmutableModuleBinding
    (environment : ModuleEnvironment) (name : String) (value : Term) :
    Option ModuleEnvironment :=
  if moduleContains environment name = false
  then some ((name, value) :: environment)
  else none

def eraseModuleBinding : ModuleEnvironment → String → ModuleEnvironment
  | [], _ => []
  | (boundName, value) :: rest, name =>
      if name = boundName
      then eraseModuleBinding rest name
      else (boundName, value) :: eraseModuleBinding rest name

def eraseManyModuleBindings : ModuleEnvironment → List String → ModuleEnvironment
  | environment, [] => environment
  | environment, name :: rest =>
      eraseManyModuleBindings (eraseModuleBinding environment name) rest

def functionEntryEnvironment
    (capturedGlobals : ModuleEnvironment)
    (locallyBoundNames : List String)
    (parameters : ModuleEnvironment) : ModuleEnvironment :=
  parameters ++ eraseManyModuleBindings capturedGlobals locallyBoundNames

def isPassiveScalarTerm (value : Term) : Bool :=
  match inferSort value with
  | some .int => true
  | some .bool => true
  | _ => false

structure ImmutableClassConstant where
  name : String
  value : Term
  requiredNames : List String

structure ClassConstantState where
  visibleBindings : ModuleEnvironment
  declaredConstants : ModuleEnvironment

def allModuleNamesReachable
    (environment : ModuleEnvironment) (names : List String) : Bool :=
  names.all (fun name => moduleContains environment name)

def insertImmutableClassConstant
    (state : ClassConstantState) (constant : ImmutableClassConstant) :
    Option ClassConstantState :=
  if allModuleNamesReachable state.visibleBindings constant.requiredNames = true &&
      moduleContains state.declaredConstants constant.name = false &&
      isPassiveScalarTerm constant.value = true
  then
    some {
      visibleBindings := (constant.name, constant.value) :: state.visibleBindings
      declaredConstants := (constant.name, constant.value) :: state.declaredConstants
    }
  else none

def executeClassConstants :
    ClassConstantState → List ImmutableClassConstant → Option ClassConstantState
  | state, [] => some state
  | state, constant :: rest =>
      match insertImmutableClassConstant state constant with
      | none => none
      | some next => executeClassConstants next rest

structure PassiveClassDefinition where
  name : String
  baseName : Option String
  constants : List ImmutableClassConstant

structure PassiveModuleNamespace where
  scalarBindings : ModuleEnvironment
  classBindings : List (String × ModuleEnvironment)
  opaqueReferences : List String

def passiveClassLookup :
    List (String × ModuleEnvironment) → String → Option ModuleEnvironment
  | [], _ => none
  | (boundName, constants) :: rest, name =>
      if name = boundName then some constants else passiveClassLookup rest name

def passiveNamespaceContainsName
    (moduleState : PassiveModuleNamespace) (name : String) : Bool :=
  moduleContains moduleState.scalarBindings name ||
    (passiveClassLookup moduleState.classBindings name).isSome ||
    moduleState.opaqueReferences.contains name

def finishPassiveClassDefinition
    (moduleState : PassiveModuleNamespace) (definition : PassiveClassDefinition) :
    Option PassiveModuleNamespace :=
  let initial : ClassConstantState := {
    visibleBindings := moduleState.scalarBindings
    declaredConstants := []
  }
  match executeClassConstants initial definition.constants with
  | none => none
  | some completed =>
      some {
        moduleState with
        classBindings :=
          (definition.name, completed.declaredConstants) :: moduleState.classBindings
      }

def definePassiveClass
    (moduleState : PassiveModuleNamespace) (definition : PassiveClassDefinition) :
    Option PassiveModuleNamespace :=
  if passiveNamespaceContainsName moduleState definition.name = true
  then none
  else
    match definition.baseName with
    | none => finishPassiveClassDefinition moduleState definition
    | some baseName =>
        match passiveClassLookup moduleState.classBindings baseName with
        | none => none
        | some _ => finishPassiveClassDefinition moduleState definition

def bindPassiveOpaqueReference
    (moduleState : PassiveModuleNamespace) (name className : String) :
    Option PassiveModuleNamespace :=
  if passiveNamespaceContainsName moduleState name = true
  then none
  else
    match passiveClassLookup moduleState.classBindings className with
    | none => none
    | some _ =>
        some { moduleState with opaqueReferences := name :: moduleState.opaqueReferences }

inductive PassiveNamespaceStatement where
  | scalarBinding : String → Term → PassiveNamespaceStatement
  | classDefinition : PassiveClassDefinition → PassiveNamespaceStatement
  | opaqueReference : String → String → PassiveNamespaceStatement

def advancePassiveNamespace
    (moduleState : PassiveModuleNamespace) (statement : PassiveNamespaceStatement) :
    Option PassiveModuleNamespace :=
  match statement with
  | .scalarBinding name value =>
      if passiveNamespaceContainsName moduleState name = true ||
          isPassiveScalarTerm value = false
      then none
      else
        match insertImmutableModuleBinding moduleState.scalarBindings name value with
        | none => none
        | some inserted => some { moduleState with scalarBindings := inserted }
  | .classDefinition definition => definePassiveClass moduleState definition
  | .opaqueReference name className => bindPassiveOpaqueReference moduleState name className

inductive PassiveNamespaceProgress where
  | running : PassiveModuleNamespace → PassiveNamespaceProgress
  | halted : PassiveModuleNamespace → PassiveNamespaceProgress

def advancePassiveNamespaceProgress
    (progress : PassiveNamespaceProgress) (statement : PassiveNamespaceStatement) :
    PassiveNamespaceProgress :=
  match progress with
  | .halted moduleState => .halted moduleState
  | .running moduleState =>
      match advancePassiveNamespace moduleState statement with
      | none => .halted moduleState
      | some next => .running next

def executePassiveNamespace :
    PassiveNamespaceProgress → List PassiveNamespaceStatement → PassiveNamespaceProgress
  | progress, [] => progress
  | progress, statement :: rest =>
      executePassiveNamespace (advancePassiveNamespaceProgress progress statement) rest

def callableCapturedScalarEnvironment
    (moduleState : PassiveModuleNamespace) : ModuleEnvironment :=
  moduleState.scalarBindings

theorem beq_some_bool_true_iff (value : Option ValueSort) :
    (value == some .bool) = true ↔ value = some .bool := by
  cases value with
  | none => simp
  | some sort => cases sort <;> simp [instBEqValueSort, valueSortBeq]

theorem beq_some_int_true_iff (value : Option ValueSort) :
    (value == some .int) = true ↔ value = some .int := by
  cases value with
  | none => simp
  | some sort => cases sort <;> simp [instBEqValueSort, valueSortBeq]

theorem beq_some_string_true_iff (value : Option ValueSort) :
    (value == some .string) = true ↔ value = some .string := by
  cases value with
  | none => simp
  | some sort => cases sort <;> simp [instBEqValueSort, valueSortBeq]

theorem beq_some_bytes_true_iff (value : Option ValueSort) :
    (value == some .bytes) = true ↔ value = some .bytes := by
  cases value with
  | none => simp
  | some sort => cases sort <;> simp [instBEqValueSort, valueSortBeq]

theorem beq_some_reference_true_iff (value : Option ValueSort) :
    (value == some .reference) = true ↔ value = some .reference := by
  cases value with
  | none => simp
  | some sort => cases sort <;> simp [instBEqValueSort, valueSortBeq]

theorem beq_some_class_true_iff (value : Option ValueSort) :
    (value == some .class) = true ↔ value = some .class := by
  cases value with
  | none => simp
  | some sort => cases sort <;> simp [instBEqValueSort, valueSortBeq]

theorem add_infers_int_only_from_int_operands
    (left right : Term)
    (accepted : inferSort (.add left right) = some .int) :
    inferSort left = some .int ∧ inferSort right = some .int := by
  simp [inferSort] at accepted
  exact ⟨(beq_some_int_true_iff _).mp accepted.1,
    (beq_some_int_true_iff _).mp accepted.2⟩

theorem subtract_infers_int_only_from_int_operands
    (left right : Term)
    (accepted : inferSort (.subtract left right) = some .int) :
    inferSort left = some .int ∧ inferSort right = some .int := by
  simp [inferSort] at accepted
  exact ⟨(beq_some_int_true_iff _).mp accepted.1,
    (beq_some_int_true_iff _).mp accepted.2⟩

theorem multiply_infers_int_only_from_int_operands
    (left right : Term)
    (accepted : inferSort (.multiply left right) = some .int) :
    inferSort left = some .int ∧ inferSort right = some .int := by
  simp [inferSort] at accepted
  exact ⟨(beq_some_int_true_iff _).mp accepted.1,
    (beq_some_int_true_iff _).mp accepted.2⟩

theorem floorDivideByPositive_infers_int_only_from_int_operand
    (value : Term)
    (divisor : Nat)
    (accepted : inferSort (.floorDivideByPositive value divisor) = some .int) :
    inferSort value = some .int ∧ divisor ≠ 0 := by
  simp [inferSort] at accepted
  exact ⟨(beq_some_int_true_iff _).mp accepted.1, accepted.2⟩

theorem less_infers_bool_only_from_int_operands
    (left right : Term)
    (accepted : inferSort (.less left right) = some .bool) :
    inferSort left = some .int ∧ inferSort right = some .int := by
  simp [inferSort] at accepted
  exact ⟨(beq_some_int_true_iff _).mp accepted.1,
    (beq_some_int_true_iff _).mp accepted.2⟩

theorem allBool_member_infers_bool
    (values : List Term)
    (accepted : allBool values = true)
    (value : Term)
    (member : value ∈ values) :
    inferSort value = some .bool := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp [allBool] at accepted
      simp at member
      cases member with
      | inl equal => exact (beq_some_bool_true_iff _).mp (by simpa [equal] using accepted.1)
      | inr tailMember => exact inductionHypothesis accepted.2 tailMember

theorem allString_member_infers_string
    (values : List Term)
    (accepted : allString values = true)
    (value : Term)
    (member : value ∈ values) :
    inferSort value = some .string := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp [allString] at accepted
      simp at member
      cases member with
      | inl equal => exact (beq_some_string_true_iff _).mp (by simpa [equal] using accepted.1)
      | inr tailMember => exact inductionHypothesis accepted.2 tailMember

theorem allBytes_member_infers_bytes
    (values : List Term)
    (accepted : allBytes values = true)
    (value : Term)
    (member : value ∈ values) :
    inferSort value = some .bytes := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp [allBytes] at accepted
      simp at member
      cases member with
      | inl equal => exact (beq_some_bytes_true_iff _).mp (by simpa [equal] using accepted.1)
      | inr tailMember => exact inductionHypothesis accepted.2 tailMember

theorem field_read_infers_only_from_reference_receiver
    (heap : Nat) (receiver : Term) (field : String) (sort : ValueSort)
    (accepted : inferSort (.fieldRead heap receiver field sort) = some sort) :
    inferSort receiver = some .reference ∧ isHeapFieldSort sort = true := by
  simp [inferSort] at accepted
  exact ⟨(beq_some_reference_true_iff _).mp accepted.1, accepted.2⟩

theorem tuple_constructor_preserves_component_sorts
    (values : List Term) (sorts : List ValueSort)
    (accepted : inferTupleSorts values = some sorts) :
    inferSort (.tuple values) = some (.tuple sorts) := by
  simp [inferSort, accepted]

theorem list_constructor_preserves_element_sort
    (values : List Term) (elementSort : ValueSort)
    (supported : isListElementSort elementSort = true)
    (accepted : allOfSort values elementSort = true) :
    inferSort (.list elementSort values) = some (.list elementSort) := by
  simp [inferSort, supported, accepted]

theorem bytes_literal_preserves_bytes_sort (values : List Nat) :
    inferSort (.bytesLiteral values) = some .bytes := by
  simp [inferSort]

theorem bytes_concat_preserves_bytes_sort
    (values : List Term)
    (accepted : allBytes values = true) :
    inferSort (.bytesConcat values) = some .bytes := by
  simp [inferSort, accepted]

theorem bytes_length_infers_int
    (value : Term)
    (accepted : inferSort value = some .bytes) :
    inferSort (.bytesLength value) = some .int := by
  simp [inferSort, accepted, instBEqValueSort, valueSortBeq]

theorem bytes_get_infers_int
    (value index : Term)
    (valueAccepted : inferSort value = some .bytes)
    (indexAccepted : inferSort index = some .int) :
    inferSort (.bytesGet value index) = some .int := by
  simp [inferSort, valueAccepted, indexAccepted, instBEqValueSort, valueSortBeq]

theorem integer_abs_term_infers_int
    (value : Term)
    (accepted : inferSort value = some .int) :
    inferSort (integerAbsTerm value) = some .int := by
  simp [integerAbsTerm, inferSort, accepted, instBEqValueSort, valueSortBeq]

theorem integer_min_term_infers_int
    (left right : Term)
    (leftAccepted : inferSort left = some .int)
    (rightAccepted : inferSort right = some .int) :
    inferSort (integerMinTerm left right) = some .int := by
  simp [integerMinTerm, inferSort, leftAccepted, rightAccepted, instBEqValueSort, valueSortBeq]

theorem integer_max_term_infers_int
    (left right : Term)
    (leftAccepted : inferSort left = some .int)
    (rightAccepted : inferSort right = some .int) :
    inferSort (integerMaxTerm left right) = some .int := by
  simp [integerMaxTerm, inferSort, leftAccepted, rightAccepted, instBEqValueSort, valueSortBeq]

theorem nonnegative_integer_power_term_infers_int
    (base : Term)
    (exponent : Nat)
    (baseAccepted : inferSort base = some .int) :
    inferSort (nonnegativeIntegerPowerTerm base exponent) = some .int := by
  induction exponent with
  | zero => simp [nonnegativeIntegerPowerTerm, inferSort]
  | succ exponent inductionHypothesis =>
      simp [nonnegativeIntegerPowerTerm, inferSort, inductionHypothesis, baseAccepted,
        instBEqValueSort, valueSortBeq]

theorem dynamic_tuple_select_term_preserves_common_sort
    (index fallback : Term)
    (choices : List (Nat × Term))
    (sort : ValueSort)
    (indexAccepted : inferSort index = some .int)
    (fallbackAccepted : inferSort fallback = some sort)
    (sortReflexive : valueSortBeq sort sort = true)
    (choicesAccepted : allIndexedOfSort choices sort) :
    inferSort (dynamicTupleSelectTerm index fallback choices) = some sort := by
  induction choices with
  | nil => simpa [dynamicTupleSelectTerm] using fallbackAccepted
  | cons choice rest inductionHypothesis =>
      rcases choice with ⟨position, value⟩
      simp [allIndexedOfSort] at choicesAccepted
      have valueAccepted : inferSort value = some sort := choicesAccepted.1
      have restAccepted : inferSort (dynamicTupleSelectTerm index fallback rest) = some sort :=
        inductionHypothesis choicesAccepted.2
      simp [dynamicTupleSelectTerm, inferSort, indexAccepted, valueAccepted, restAccepted,
        instBEqValueSort, valueSortBeq, sortReflexive]

theorem immutable_module_binding_inserts_only_when_absent
    (environment : ModuleEnvironment)
    (name : String)
    (value : Term)
    (missing : moduleContains environment name = false) :
    insertImmutableModuleBinding environment name value =
      some ((name, value) :: environment) := by
  simp [insertImmutableModuleBinding, missing]

theorem module_contains_false_iff_lookup_none
    (environment : ModuleEnvironment)
    (name : String) :
    moduleContains environment name = false ↔ moduleLookup environment name = none := by
  induction environment with
  | nil => simp [moduleContains, moduleLookup]
  | cons binding rest inductionHypothesis =>
      rcases binding with ⟨boundName, value⟩
      by_cases same : name = boundName
      · simp [moduleContains, moduleLookup, same]
      · simp [moduleContains, moduleLookup, same, inductionHypothesis]

theorem immutable_module_binding_refuses_when_present
    (environment : ModuleEnvironment)
    (name : String)
    (value : Term)
    (present : moduleContains environment name = true) :
    insertImmutableModuleBinding environment name value = none := by
  simp [insertImmutableModuleBinding, present]

theorem inserted_module_binding_is_visible
    (environment : ModuleEnvironment)
    (name : String)
    (value : Term) :
    moduleLookup ((name, value) :: environment) name = some value := by
  simp [moduleLookup]

theorem inserted_module_binding_preserves_other_names
    (environment : ModuleEnvironment)
    (name other : String)
    (value : Term)
    (different : other ≠ name) :
    moduleLookup ((name, value) :: environment) other =
      moduleLookup environment other := by
  simp [moduleLookup, different]

theorem immutable_module_binding_fresh_lookup_preserves_sort
    (environment : ModuleEnvironment)
    (name : String)
    (value : Term)
    (sort : ValueSort)
    (missing : moduleContains environment name = false)
    (valueAccepted : inferSort value = some sort) :
    ∃ inserted,
      insertImmutableModuleBinding environment name value = some inserted ∧
      moduleLookup inserted name = some value ∧
      inferSort value = some sort := by
  refine ⟨(name, value) :: environment, ?_, ?_, valueAccepted⟩
  · exact immutable_module_binding_inserts_only_when_absent environment name value missing
  · exact inserted_module_binding_is_visible environment name value

theorem erased_module_binding_is_absent
    (environment : ModuleEnvironment)
    (name : String) :
    moduleLookup (eraseModuleBinding environment name) name = none := by
  induction environment with
  | nil => simp [eraseModuleBinding, moduleLookup]
  | cons binding rest inductionHypothesis =>
      rcases binding with ⟨boundName, value⟩
      by_cases same : name = boundName
      · subst boundName
        simpa [eraseModuleBinding] using inductionHypothesis
      · simp [eraseModuleBinding, moduleLookup, same, inductionHypothesis]

theorem erased_module_binding_preserves_other_names
    (environment : ModuleEnvironment)
    (erasedName otherName : String)
    (different : otherName ≠ erasedName) :
    moduleLookup (eraseModuleBinding environment erasedName) otherName =
      moduleLookup environment otherName := by
  induction environment with
  | nil => simp [eraseModuleBinding, moduleLookup]
  | cons binding rest inductionHypothesis =>
      rcases binding with ⟨boundName, value⟩
      by_cases erasedHere : erasedName = boundName
      · subst boundName
        simpa [eraseModuleBinding, moduleLookup, different] using inductionHypothesis
      · by_cases otherHere : otherName = boundName
        · simp [eraseModuleBinding, moduleLookup, erasedHere, otherHere]
        · simp [eraseModuleBinding, moduleLookup, erasedHere, otherHere,
            inductionHypothesis]

theorem module_lookup_erased_binding
    (environment : ModuleEnvironment)
    (erasedName name : String) :
    moduleLookup (eraseModuleBinding environment erasedName) name =
      if name = erasedName then none else moduleLookup environment name := by
  by_cases same : name = erasedName
  · subst erasedName
    simp [erased_module_binding_is_absent]
  · simp [same, erased_module_binding_preserves_other_names environment erasedName name same]

theorem module_lookup_erased_many_bindings
    (environment : ModuleEnvironment)
    (erasedNames : List String)
    (name : String) :
    moduleLookup (eraseManyModuleBindings environment erasedNames) name =
      if name ∈ erasedNames then none else moduleLookup environment name := by
  induction erasedNames generalizing environment with
  | nil => simp [eraseManyModuleBindings]
  | cons erasedName rest inductionHypothesis =>
      by_cases inRest : name ∈ rest
      · simp [eraseManyModuleBindings, inductionHypothesis, inRest]
      · by_cases same : name = erasedName
        · subst erasedName
          rw [eraseManyModuleBindings, inductionHypothesis]
          simp [inRest, erased_module_binding_is_absent]
        · simp [eraseManyModuleBindings, inductionHypothesis, inRest, same,
            module_lookup_erased_binding]

theorem module_lookup_append
    (left right : ModuleEnvironment)
    (name : String) :
    moduleLookup (left ++ right) name =
      match moduleLookup left name with
      | some value => some value
      | none => moduleLookup right name := by
  induction left with
  | nil => simp [moduleLookup]
  | cons binding rest inductionHypothesis =>
      rcases binding with ⟨boundName, value⟩
      by_cases same : name = boundName
      · simp [moduleLookup, same]
      · simp [moduleLookup, same, inductionHypothesis]

theorem function_entry_parameter_shadows_captured_global
    (capturedGlobals : ModuleEnvironment)
    (locallyBoundNames : List String)
    (parameters : ModuleEnvironment)
    (name : String)
    (value : Term)
    (parameterFound : moduleLookup parameters name = some value) :
    moduleLookup
        (functionEntryEnvironment capturedGlobals locallyBoundNames parameters)
        name = some value := by
  simp [functionEntryEnvironment, module_lookup_append, parameterFound]

theorem function_entry_unparameterized_local_is_absent
    (capturedGlobals : ModuleEnvironment)
    (locallyBoundNames : List String)
    (parameters : ModuleEnvironment)
    (name : String)
    (parameterMissing : moduleLookup parameters name = none)
    (locallyBound : name ∈ locallyBoundNames) :
    moduleLookup
        (functionEntryEnvironment capturedGlobals locallyBoundNames parameters)
        name = none := by
  simp [functionEntryEnvironment, module_lookup_append, parameterMissing,
    module_lookup_erased_many_bindings, locallyBound]

theorem function_entry_preserves_untouched_captured_global
    (capturedGlobals : ModuleEnvironment)
    (locallyBoundNames : List String)
    (parameters : ModuleEnvironment)
    (name : String)
    (parameterMissing : moduleLookup parameters name = none)
    (notLocallyBound : name ∉ locallyBoundNames) :
    moduleLookup
        (functionEntryEnvironment capturedGlobals locallyBoundNames parameters)
        name = moduleLookup capturedGlobals name := by
  simp [functionEntryEnvironment, module_lookup_append, parameterMissing,
    module_lookup_erased_many_bindings, notLocallyBound]

theorem all_module_names_reachable_false_of_missing
    (environment : ModuleEnvironment)
    (names : List String)
    (missingName : String)
    (member : missingName ∈ names)
    (missing : moduleContains environment missingName = false) :
    allModuleNamesReachable environment names = false := by
  induction names with
  | nil => simp at member
  | cons name rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with same | inRest
      · subst name
        change (moduleContains environment missingName &&
          allModuleNamesReachable environment rest) = false
        rw [missing]
        simp
      · have restUnreachable := inductionHypothesis inRest
        change (moduleContains environment name &&
          allModuleNamesReachable environment rest) = false
        rw [restUnreachable]
        simp

theorem immutable_class_constant_inserts_when_reachable
    (state : ClassConstantState)
    (constant : ImmutableClassConstant)
    (reachable :
      allModuleNamesReachable state.visibleBindings constant.requiredNames = true)
    (fresh : moduleContains state.declaredConstants constant.name = false)
    (scalar : isPassiveScalarTerm constant.value = true) :
    insertImmutableClassConstant state constant = some {
      visibleBindings := (constant.name, constant.value) :: state.visibleBindings
      declaredConstants := (constant.name, constant.value) :: state.declaredConstants
    } := by
  simp [insertImmutableClassConstant, reachable, fresh, scalar]

theorem immutable_class_constant_refuses_duplicate
    (state : ClassConstantState)
    (constant : ImmutableClassConstant)
    (duplicate : moduleContains state.declaredConstants constant.name = true) :
    insertImmutableClassConstant state constant = none := by
  simp [insertImmutableClassConstant, duplicate]

theorem immutable_class_constant_refuses_undefined_name
    (state : ClassConstantState)
    (constant : ImmutableClassConstant)
    (missingName : String)
    (required : missingName ∈ constant.requiredNames)
    (missing : moduleContains state.visibleBindings missingName = false) :
    insertImmutableClassConstant state constant = none := by
  have unreachable := all_module_names_reachable_false_of_missing
    state.visibleBindings constant.requiredNames missingName required missing
  simp [insertImmutableClassConstant, unreachable]

theorem inserted_class_constant_is_visible_and_declared
    (state : ClassConstantState)
    (constant : ImmutableClassConstant) :
    moduleLookup
        ((constant.name, constant.value) :: state.visibleBindings)
        constant.name = some constant.value ∧
      moduleLookup
        ((constant.name, constant.value) :: state.declaredConstants)
        constant.name = some constant.value := by
  simp [moduleLookup]

theorem failed_class_constant_stops_remaining_constants
    (state : ClassConstantState)
    (constant : ImmutableClassConstant)
    (remaining : List ImmutableClassConstant)
    (failed : insertImmutableClassConstant state constant = none) :
    executeClassConstants state (constant :: remaining) = none := by
  simp [executeClassConstants, failed]

theorem passive_class_refuses_undefined_base
    (moduleState : PassiveModuleNamespace)
    (definition : PassiveClassDefinition)
    (baseName : String)
    (declaredBase : definition.baseName = some baseName)
    (missingBase : passiveClassLookup moduleState.classBindings baseName = none) :
    definePassiveClass moduleState definition = none := by
  simp [definePassiveClass, declaredBase, missingBase]

theorem passive_class_refuses_failed_class_constants
    (moduleState : PassiveModuleNamespace)
    (definition : PassiveClassDefinition)
    (failed : executeClassConstants {
      visibleBindings := moduleState.scalarBindings
      declaredConstants := []
    } definition.constants = none) :
    definePassiveClass moduleState definition = none := by
  unfold definePassiveClass
  split
  · rfl
  · cases definition.baseName with
    | none => simp [finishPassiveClassDefinition, failed]
    | some baseName =>
        cases classLookup : passiveClassLookup moduleState.classBindings baseName <;>
          simp [classLookup, finishPassiveClassDefinition, failed]

theorem execute_passive_namespace_from_halted
    (moduleState : PassiveModuleNamespace)
    (statements : List PassiveNamespaceStatement) :
    executePassiveNamespace (.halted moduleState) statements = .halted moduleState := by
  induction statements with
  | nil => simp [executePassiveNamespace]
  | cons statement rest inductionHypothesis =>
      simp [executePassiveNamespace, advancePassiveNamespaceProgress,
        inductionHypothesis]

theorem failed_passive_class_definition_halts_later_statements
    (moduleState : PassiveModuleNamespace)
    (definition : PassiveClassDefinition)
    (laterStatements : List PassiveNamespaceStatement)
    (failed : definePassiveClass moduleState definition = none) :
    executePassiveNamespace
        (.running moduleState)
        (.classDefinition definition :: laterStatements) = .halted moduleState := by
  simp [executePassiveNamespace, advancePassiveNamespaceProgress,
    advancePassiveNamespace, failed, execute_passive_namespace_from_halted]

theorem passive_opaque_reference_is_not_captured
    (moduleState : PassiveModuleNamespace)
    (name className : String)
    (classConstants : ModuleEnvironment)
    (fresh : passiveNamespaceContainsName moduleState name = false)
    (classFound :
      passiveClassLookup moduleState.classBindings className = some classConstants)
    (scalarMissing : moduleLookup moduleState.scalarBindings name = none) :
    let extended := {
      moduleState with opaqueReferences := name :: moduleState.opaqueReferences
    }
    bindPassiveOpaqueReference moduleState name className = some extended ∧
      callableCapturedScalarEnvironment extended =
        callableCapturedScalarEnvironment moduleState ∧
      moduleLookup (callableCapturedScalarEnvironment extended) name = none := by
  simp [bindPassiveOpaqueReference, fresh, classFound,
    callableCapturedScalarEnvironment, scalarMissing]

theorem range_literal_preserves_range_sort (values : List Int) :
    inferSort (.rangeLiteral values) = some .range := by
  simp [inferSort]

theorem list_get_infers_declared_element_sort
    (value index : Term) (elementSort : ValueSort)
    (listAccepted : inferSort value = some (.list elementSort))
    (indexAccepted : inferSort index = some .int) :
    inferSort (.listGet value index) = some elementSort := by
  simp [inferSort, listAccepted, indexAccepted, instBEqValueSort, valueSortBeq]

theorem permission_infers_bool_only_for_valid_fraction
    (mask : Nat) (receiver : Term) (field : String) (numerator denominator : Nat)
    (accepted : inferSort (.permissionAtLeast mask receiver field numerator denominator) = some .bool) :
    inferSort receiver = some .reference ∧ denominator ≠ 0 ∧ numerator ≤ denominator := by
  simp [inferSort] at accepted
  exact ⟨(beq_some_reference_true_iff _).mp accepted.1, accepted.2⟩

theorem positive_permission_infers_bool_only_for_reference_receiver
    (mask : Nat) (receiver : Term) (field : String)
    (accepted : inferSort (.permissionPositive mask receiver field) = some .bool) :
    inferSort receiver = some .reference := by
  simp [inferSort] at accepted
  exact (beq_some_reference_true_iff _).mp accepted

theorem permission_mask_valid_requires_a_named_field
    (mask : Nat) (field : String)
    (accepted : inferSort (.permissionMaskValid mask field) = some .bool) :
    field.isEmpty = false := by
  simp [inferSort] at accepted
  simpa using accepted

theorem permission_mask_transition_advances_and_names_the_field
    (preMask postMask : Nat) (field : String)
    (consumed produced : List (Term × Nat × Nat))
    (accepted :
      inferSort (.permissionMaskTransition preMask postMask field consumed produced) = some .bool) :
    preMask ≠ postMask ∧ field.isEmpty = false := by
  simp [inferSort] at accepted
  exact ⟨accepted.1, by simpa using accepted.2.1⟩

theorem nominal_reference_infers_reference_only_for_nonempty_class
    (name className : String)
    (accepted : inferSort (.nominalReference name className) = some .reference) :
    className.isEmpty = false := by
  simp [inferSort] at accepted
  simpa using accepted

theorem class_literal_infers_class_only_for_nonempty_name
    (className : String)
    (accepted : inferSort (.classLiteral className) = some .class) :
    className.isEmpty = false := by
  simp [inferSort] at accepted
  simpa using accepted

theorem runtime_class_requires_reference
    (value : Term)
    (accepted : inferSort (.runtimeClass value) = some .class) :
    inferSort value = some .reference := by
  simp [inferSort] at accepted
  exact (beq_some_reference_true_iff _).mp accepted

theorem class_subtype_requires_class_operands
    (actual expected : Term)
    (accepted : inferSort (.classSubtype actual expected) = some .bool) :
    inferSort actual = some .class ∧ inferSort expected = some .class := by
  simp [inferSort] at accepted
  exact ⟨
    (beq_some_class_true_iff _).mp accepted.1,
    (beq_some_class_true_iff _).mp accepted.2
  ⟩

theorem inferred_sort_is_unique
    (term : Term) (first second : ValueSort)
    (firstProof : inferSort term = some first)
    (secondProof : inferSort term = some second) :
    first = second := by
  exact Option.some.inj (firstProof.symm.trans secondProof)

end Maledictus
