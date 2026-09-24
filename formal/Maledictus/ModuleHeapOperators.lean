import Maledictus.EffectfulHeapExpressions

namespace Maledictus

/-!
# Verified module heap calls and operator paths

This executable model covers the additional `test_operators` semantics built on top of the v57
effectful-expression state.  A reusable module summary has exactly one non-null nominal receiver,
one scalar argument, one directly modified integer field, a verified normal exit, and equal full
permission before and after the call.  The result is the scalar argument, as in `updating_id` and
`updating_id_int`.

The model assumes that frontend name resolution has selected the canonical module function and
that `actualClass` is its resolved nominal identity.  It intentionally does not model subtyping,
alias-derived frames, exceptional paths, recursive summaries, partial permissions, dynamic
attribute dispatch, or effectful argument evaluation.  Those cases must be refused before this
summary is constructed.  The finite `fields` and `fullPermissions` collections remain the
authoritative heap and mask inputs inherited from `EffectfulHeapExpressions`.
-/

inductive ModuleHeapExitShape where
  | normalOnly
  | mayRaise
  deriving DecidableEq, BEq

def moduleHeapScalarSortSupported : ValueSort → Bool
  | .bool | .int => true
  | _ => false

structure ModuleHeapCallSummary where
  name : String
  receiverClass : String
  field : String
  parameterSort : ValueSort
  returnSort : ValueSort
  fieldDelta : Int
  verified : Bool
  exitShape : ModuleHeapExitShape
  requiresFullPermission : Bool
  returnsFullPermission : Bool

structure ModuleHeapCallRequest where
  summary : ModuleHeapCallSummary
  actualReceiver : String
  actualClass : String
  scalarArgument : Term

structure ModuleHeapCallResult where
  value : Term
  oldValue : Int
  newValue : Int
  oldFieldRead : Term
  currentFieldRead : Term
  postcondition : Term
  state : EffectfulHeapExpressionState

def moduleHeapCallSummaryAccepted (summary : ModuleHeapCallSummary) : Bool :=
  !summary.name.isEmpty &&
    !summary.receiverClass.isEmpty &&
    !summary.field.isEmpty &&
    moduleHeapScalarSortSupported summary.parameterSort &&
    summary.parameterSort == summary.returnSort &&
    summary.verified &&
    summary.exitShape == .normalOnly &&
    summary.requiresFullPermission &&
    summary.returnsFullPermission

def applyModuleHeapCallSummary
    (request : ModuleHeapCallRequest) (state : EffectfulHeapExpressionState) :
    Option ModuleHeapCallResult :=
  if !moduleHeapCallSummaryAccepted request.summary then none
  else if request.actualReceiver.isEmpty then none
  else if request.actualClass != request.summary.receiverClass then none
  else if inferSort request.scalarArgument != some request.summary.parameterSort then none
  else if !hasFullEffectfulFieldPermission state
      request.actualReceiver request.summary.field then none
  else
    match lookupEffectfulIntegerField state.fields
        request.actualReceiver request.summary.field with
    | none => none
    | some oldValue =>
        let newValue := oldValue + request.summary.fieldDelta
        let receiver := Term.nominalReference request.actualReceiver request.actualClass
        let oldFieldRead := Term.fieldRead state.heap receiver request.summary.field .int
        let currentFieldRead :=
          Term.fieldRead (state.heap + 1) receiver request.summary.field .int
        some {
          value := request.scalarArgument
          oldValue
          newValue
          oldFieldRead
          currentFieldRead
          postcondition := .equal currentFieldRead
            (.add oldFieldRead (.intLiteral request.summary.fieldDelta))
          state := {
            state with
              heap := state.heap + 1
              fields := writeEffectfulIntegerField state.fields
                request.actualReceiver request.summary.field newValue
              trace := state.trace ++ [
                .receiverEvaluated request.actualReceiver,
                .fieldRead request.actualReceiver request.summary.field oldValue,
                .rightOperandEvaluated request.summary.fieldDelta,
                .fieldWritten request.actualReceiver request.summary.field newValue
              ]
          }
        }

theorem unverified_module_heap_summary_refuses
    (request : ModuleHeapCallRequest) (state : EffectfulHeapExpressionState)
    (unverified : request.summary.verified = false) :
    applyModuleHeapCallSummary request state = none := by
  simp [applyModuleHeapCallSummary, moduleHeapCallSummaryAccepted, unverified]

theorem exceptional_module_heap_summary_refuses
    (request : ModuleHeapCallRequest) (state : EffectfulHeapExpressionState)
    (exceptional : request.summary.exitShape = .mayRaise) :
    applyModuleHeapCallSummary request state = none := by
  have exitRejected : (request.summary.exitShape == .normalOnly) = false := by
    rw [exceptional]
    decide
  simp [applyModuleHeapCallSummary, moduleHeapCallSummaryAccepted, exitRejected]

theorem module_heap_summary_nominal_mismatch_refuses
    (request : ModuleHeapCallRequest) (state : EffectfulHeapExpressionState)
    (acceptedSummary : moduleHeapCallSummaryAccepted request.summary = true)
    (receiverNamed : request.actualReceiver.isEmpty = false)
    (mismatch : request.actualClass != request.summary.receiverClass) :
    applyModuleHeapCallSummary request state = none := by
  simp [applyModuleHeapCallSummary, acceptedSummary, receiverNamed, mismatch]

theorem module_heap_summary_without_full_permission_refuses
    (request : ModuleHeapCallRequest) (state : EffectfulHeapExpressionState)
    (acceptedSummary : moduleHeapCallSummaryAccepted request.summary = true)
    (receiverNamed : request.actualReceiver.isEmpty = false)
    (classMatch : request.actualClass = request.summary.receiverClass)
    (argumentTyped : inferSort request.scalarArgument = some request.summary.parameterSort)
    (missing : hasFullEffectfulFieldPermission state
      request.actualReceiver request.summary.field = false) :
    applyModuleHeapCallSummary request state = none := by
  simp [applyModuleHeapCallSummary, acceptedSummary, receiverNamed, classMatch,
    argumentTyped, missing]

theorem successful_module_heap_call_uses_distinct_pre_and_post_heaps
    (request : ModuleHeapCallRequest) (state : EffectfulHeapExpressionState)
    (result : ModuleHeapCallResult)
    (accepted : applyModuleHeapCallSummary request state = some result) :
    result.oldFieldRead = .fieldRead state.heap
        (.nominalReference request.actualReceiver request.actualClass)
        request.summary.field .int ∧
      result.currentFieldRead = .fieldRead (state.heap + 1)
        (.nominalReference request.actualReceiver request.actualClass)
        request.summary.field .int ∧
      result.state.heap = state.heap + 1 ∧
      result.state.mask = state.mask := by
  unfold applyModuleHeapCallSummary at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  next oldValue found =>
    injection accepted with resultEq
    subst result
    simp

theorem successful_module_heap_call_copies_argument_and_instantiates_old
    (request : ModuleHeapCallRequest) (state : EffectfulHeapExpressionState)
    (result : ModuleHeapCallResult)
    (accepted : applyModuleHeapCallSummary request state = some result) :
    result.value = request.scalarArgument ∧
      result.newValue = result.oldValue + request.summary.fieldDelta ∧
      result.postcondition = .equal result.currentFieldRead
        (.add result.oldFieldRead (.intLiteral request.summary.fieldDelta)) := by
  unfold applyModuleHeapCallSummary at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  next oldValue found =>
    injection accepted with resultEq
    subst result
    simp

/-! Bool-only Python `and` / `or`.  The second operand is executed only when selected. -/

inductive EffectfulBoolOperand where
  | literal (value : Bool)
  | moduleCall (request : ModuleHeapCallRequest)

structure EffectfulBoolOperandResult where
  value : Bool
  state : EffectfulHeapExpressionState

def executeEffectfulBoolOperand
    (operand : EffectfulBoolOperand) (state : EffectfulHeapExpressionState) :
    Option EffectfulBoolOperandResult :=
  match operand with
  | .literal value => some { value, state }
  | .moduleCall request =>
      match applyModuleHeapCallSummary request state with
      | some result =>
          match result.value with
          | .boolLiteral value => some { value, state := result.state }
          | _ => none
      | none => none

inductive EffectfulBoolOperator where
  | and
  | or

def executeEffectfulBoolShortCircuit
    (operator : EffectfulBoolOperator)
    (left right : EffectfulBoolOperand)
    (state : EffectfulHeapExpressionState) : Option EffectfulBoolOperandResult :=
  match executeEffectfulBoolOperand left state with
  | none => none
  | some leftResult =>
      match operator, leftResult.value with
      | .and, false => some leftResult
      | .and, true => executeEffectfulBoolOperand right leftResult.state
      | .or, true => some leftResult
      | .or, false => executeEffectfulBoolOperand right leftResult.state

def pureEffectfulBoolOperand : EffectfulBoolOperand → Option Bool
  | .literal value => some value
  | .moduleCall _ => none

def lowerEffectfulBoolShortCircuitAsEager
    (operator : EffectfulBoolOperator)
    (left right : EffectfulBoolOperand) : Option Bool :=
  match pureEffectfulBoolOperand left, pureEffectfulBoolOperand right with
  | some leftValue, some rightValue =>
      some (match operator with
        | .and => leftValue && rightValue
        | .or => leftValue || rightValue)
  | _, _ => none

theorem boolean_and_false_executes_only_left
    (left right : EffectfulBoolOperand) (state : EffectfulHeapExpressionState)
    (leftResult : EffectfulBoolOperandResult)
    (leftExecuted : executeEffectfulBoolOperand left state = some leftResult)
    (falseResult : leftResult.value = false) :
    executeEffectfulBoolShortCircuit .and left right state = some leftResult := by
  simp [executeEffectfulBoolShortCircuit, leftExecuted, falseResult]

theorem boolean_and_true_executes_selected_right
    (left right : EffectfulBoolOperand) (state : EffectfulHeapExpressionState)
    (leftResult rightResult : EffectfulBoolOperandResult)
    (leftExecuted : executeEffectfulBoolOperand left state = some leftResult)
    (trueResult : leftResult.value = true)
    (rightExecuted : executeEffectfulBoolOperand right leftResult.state = some rightResult) :
    executeEffectfulBoolShortCircuit .and left right state = some rightResult := by
  simp [executeEffectfulBoolShortCircuit, leftExecuted, trueResult, rightExecuted]

theorem boolean_or_true_executes_only_left
    (left right : EffectfulBoolOperand) (state : EffectfulHeapExpressionState)
    (leftResult : EffectfulBoolOperandResult)
    (leftExecuted : executeEffectfulBoolOperand left state = some leftResult)
    (trueResult : leftResult.value = true) :
    executeEffectfulBoolShortCircuit .or left right state = some leftResult := by
  simp [executeEffectfulBoolShortCircuit, leftExecuted, trueResult]

theorem boolean_or_false_executes_selected_right
    (left right : EffectfulBoolOperand) (state : EffectfulHeapExpressionState)
    (leftResult rightResult : EffectfulBoolOperandResult)
    (leftExecuted : executeEffectfulBoolOperand left state = some leftResult)
    (falseResult : leftResult.value = false)
    (rightExecuted : executeEffectfulBoolOperand right leftResult.state = some rightResult) :
    executeEffectfulBoolShortCircuit .or left right state = some rightResult := by
  simp [executeEffectfulBoolShortCircuit, leftExecuted, falseResult, rightExecuted]

theorem eager_boolean_lowering_refuses_effectful_left
    (operator : EffectfulBoolOperator) (request : ModuleHeapCallRequest)
    (right : EffectfulBoolOperand) :
    lowerEffectfulBoolShortCircuitAsEager operator (.moduleCall request) right = none := by
  rfl

theorem eager_boolean_lowering_refuses_effectful_right
    (operator : EffectfulBoolOperator) (left : EffectfulBoolOperand)
    (request : ModuleHeapCallRequest) :
    lowerEffectfulBoolShortCircuitAsEager operator left (.moduleCall request) = none := by
  cases left <;> rfl

/-! Positive-literal Python modulo is lowered through the already typed floor-division term. -/

def lowerPythonModuloByPositiveLiteral (value : Term) (divisor : Nat) : Option Term :=
  if inferSort value != some .int || divisor = 0 then none
  else some (.subtract value
    (.multiply (.floorDivideByPositive value divisor) (.intLiteral (Int.ofNat divisor))))

def pythonModuloByPositiveLiteralValue (value : Int) (divisor : Nat) : Option Int :=
  if divisor = 0 then none
  else
    let positiveDivisor := Int.ofNat divisor
    some (value - (value / positiveDivisor) * positiveDivisor)

theorem positive_literal_modulo_has_floor_division_shape
    (value : Term) (divisor : Nat)
    (typed : inferSort value = some .int) (positive : divisor ≠ 0) :
    lowerPythonModuloByPositiveLiteral value divisor = some
      (.subtract value
        (.multiply (.floorDivideByPositive value divisor) (.intLiteral (Int.ofNat divisor)))) := by
  have typeAccepted : (inferSort value != some .int) = false := by
    rw [typed]
    decide
  simp [lowerPythonModuloByPositiveLiteral, typeAccepted, positive]

theorem positive_literal_modulo_result_is_integer
    (value result : Term) (divisor : Nat)
    (typed : inferSort value = some .int) (positive : divisor ≠ 0)
    (lowered : lowerPythonModuloByPositiveLiteral value divisor = some result) :
    inferSort result = some .int := by
  rw [positive_literal_modulo_has_floor_division_shape value divisor typed positive] at lowered
  injection lowered with resultEq
  subst result
  have valueAccepted : (inferSort value == some .int) = true :=
    (beq_some_int_true_iff _).mpr typed
  have floorTyped : inferSort (.floorDivideByPositive value divisor) = some .int := by
    simp [inferSort, valueAccepted, positive]
  have literalTyped : inferSort (.intLiteral (Int.ofNat divisor)) = some .int := rfl
  have productTyped : inferSort
      (.multiply (.floorDivideByPositive value divisor)
        (.intLiteral (Int.ofNat divisor))) = some .int := by
    change (if inferSort (.floorDivideByPositive value divisor) == some ValueSort.int &&
        inferSort (.intLiteral (Int.ofNat divisor)) == some ValueSort.int then
      some ValueSort.int else none) = some ValueSort.int
    rw [floorTyped, literalTyped]
    rfl
  change (if inferSort value == some ValueSort.int &&
      inferSort (.multiply (.floorDivideByPositive value divisor)
        (.intLiteral (Int.ofNat divisor))) == some ValueSort.int then
      some ValueSort.int else none) = some ValueSort.int
  rw [typed, productTyped]
  rfl

theorem negative_dividend_python_modulo_example :
    pythonModuloByPositiveLiteralValue (-13) 5 = some 2 := by
  decide

end Maledictus
