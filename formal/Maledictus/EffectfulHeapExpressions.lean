import Maledictus.HeapControl

namespace Maledictus

/-!
# Permission-safe effectful heap expressions

This module is an executable model for two v57 expression forms: integer field `AugAssign` and
conditional expressions whose selected branch may perform that update.  Evaluation events are
part of the state, so receiver-once and Python evaluation order are consequences of execution,
not caller-supplied Boolean claims.  Symbolic conditionals retain two branch-local states; only
their compatible result values are joined.

The model starts after the frontend has proved that a receiver identity denotes a non-null
ordinary source object, that the named field is an integer field with ordinary attribute
dispatch, and that the right operand is a total integer value.  `fullPermissions` and `fields`
are the authoritative finite input state for this slice.  Python-AST correspondence, alias
analysis, the truth of symbolic guards, and SMT validity remain frontend/kernel assumptions.
No theorem below authorizes merging branch heaps or masks.
-/

inductive EffectfulHeapEvent where
  | conditionEvaluated
  | thenBranchSelected
  | elseBranchSelected
  | receiverEvaluated (receiver : String)
  | fieldRead (receiver field : String) (value : Int)
  | rightOperandEvaluated (value : Int)
  | fieldWritten (receiver field : String) (value : Int)
  deriving DecidableEq

structure EffectfulIntegerField where
  receiver : String
  field : String
  value : Int
  deriving DecidableEq

structure EffectfulHeapExpressionState where
  heap : Nat
  mask : Nat
  fields : List EffectfulIntegerField
  fullPermissions : List (String × String)
  trace : List EffectfulHeapEvent
  deriving DecidableEq

def lookupEffectfulIntegerField :
    List EffectfulIntegerField → String → String → Option Int
  | [], _, _ => none
  | current :: rest, receiver, field =>
      if current.receiver == receiver && current.field == field then some current.value
      else lookupEffectfulIntegerField rest receiver field

def writeEffectfulIntegerField :
    List EffectfulIntegerField → String → String → Int → List EffectfulIntegerField
  | [], _, _, _ => []
  | current :: rest, receiver, field, value =>
      if current.receiver == receiver && current.field == field then
        { current with value } :: rest
      else current :: writeEffectfulIntegerField rest receiver field value

def hasFullEffectfulFieldPermission
    (state : EffectfulHeapExpressionState) (receiver field : String) : Bool :=
  state.fullPermissions.contains (receiver, field)

inductive EffectfulIntegerAugOperator where
  | add
  | subtract
  | multiply
  deriving DecidableEq

def applyEffectfulIntegerAugOperator : EffectfulIntegerAugOperator → Int → Int → Int
  | .add, left, right => left + right
  | .subtract, left, right => left - right
  | .multiply, left, right => left * right

structure EffectfulFieldAugAssign where
  receiver : String
  field : String
  operator : EffectfulIntegerAugOperator
  rightOperand : Int
  deriving DecidableEq

structure EffectfulFieldAugAssignResult where
  value : Int
  state : EffectfulHeapExpressionState
  deriving DecidableEq

def executeEffectfulFieldAugAssign
    (request : EffectfulFieldAugAssign) (state : EffectfulHeapExpressionState) :
    Option EffectfulFieldAugAssignResult :=
  if request.receiver.isEmpty || request.field.isEmpty then none
  else if !hasFullEffectfulFieldPermission state request.receiver request.field then none
  else
    match lookupEffectfulIntegerField state.fields request.receiver request.field with
    | none => none
    | some oldValue =>
        let value := applyEffectfulIntegerAugOperator
          request.operator oldValue request.rightOperand
        some {
          value
          state := {
            state with
              heap := state.heap + 1
              fields := writeEffectfulIntegerField state.fields
                request.receiver request.field value
              trace := state.trace ++ [
                .receiverEvaluated request.receiver,
                .fieldRead request.receiver request.field oldValue,
                .rightOperandEvaluated request.rightOperand,
                .fieldWritten request.receiver request.field value
              ]
          }
        }

inductive EffectfulConditionalBranch where
  | boolean (value : Bool)
  | integer (value : Int)
  | unit
  | fieldAugAssign (request : EffectfulFieldAugAssign)
  deriving DecidableEq

def effectfulConditionalBranchType : EffectfulConditionalBranch → HeapConditionalType
  | .boolean _ => .scalar .bool
  | .integer _ | .fieldAugAssign _ => .scalar .int
  | .unit => .scalar .unit

structure EffectfulConditionalBranchResult where
  value : Term
  valueType : HeapConditionalType
  state : EffectfulHeapExpressionState

def executeEffectfulConditionalBranch
    (branch : EffectfulConditionalBranch) (state : EffectfulHeapExpressionState) :
    Option EffectfulConditionalBranchResult :=
  match branch with
  | .boolean value => some { value := .boolLiteral value, valueType := .scalar .bool, state }
  | .integer value => some { value := .intLiteral value, valueType := .scalar .int, state }
  | .unit => some { value := .unitLiteral, valueType := .scalar .unit, state }
  | .fieldAugAssign request =>
      match executeEffectfulFieldAugAssign request state with
      | none => none
      | some result => some {
          value := .intLiteral result.value
          valueType := .scalar .int
          state := result.state
        }

def effectfulConditionalValueAtJoinedType
    (result : EffectfulConditionalBranchResult) (joinedType : HeapConditionalType) : Term :=
  match result.valueType, joinedType with
  | .scalar .bool, .scalar .int => promoteHeapConditionalBoolToInt result.value
  | _, _ => result.value

inductive EffectfulConditionalDecision where
  | concrete (value : Bool)
  | symbolic (condition : Term)

structure EffectfulConditionalPath where
  guard : Term
  value : Term
  valueType : HeapConditionalType
  state : EffectfulHeapExpressionState

structure EffectfulConditionalResult where
  paths : List EffectfulConditionalPath
  joinedValue : Term
  joinedType : HeapConditionalType

def appendEffectfulHeapEvents
    (state : EffectfulHeapExpressionState) (events : List EffectfulHeapEvent) :
    EffectfulHeapExpressionState :=
  { state with trace := state.trace ++ events }

def executeEffectfulConditional
    (decision : EffectfulConditionalDecision)
    (thenBranch elseBranch : EffectfulConditionalBranch)
    (state : EffectfulHeapExpressionState) : Option EffectfulConditionalResult :=
  match joinHeapConditionalTypes
      (effectfulConditionalBranchType thenBranch)
      (effectfulConditionalBranchType elseBranch) .unavailable with
  | none => none
  | some joinedType =>
      let conditionState := appendEffectfulHeapEvents state [.conditionEvaluated]
      match decision with
      | .concrete true =>
          let thenState := appendEffectfulHeapEvents conditionState [.thenBranchSelected]
          match executeEffectfulConditionalBranch thenBranch thenState with
          | none => none
          | some thenResult =>
              let value := effectfulConditionalValueAtJoinedType thenResult joinedType
              some {
                paths := [{
                  guard := .boolLiteral true
                  value
                  valueType := joinedType
                  state := thenResult.state
                }]
                joinedValue := value
                joinedType
              }
      | .concrete false =>
          let elseState := appendEffectfulHeapEvents conditionState [.elseBranchSelected]
          match executeEffectfulConditionalBranch elseBranch elseState with
          | none => none
          | some elseResult =>
              let value := effectfulConditionalValueAtJoinedType elseResult joinedType
              some {
                paths := [{
                  guard := .boolLiteral true
                  value
                  valueType := joinedType
                  state := elseResult.state
                }]
                joinedValue := value
                joinedType
              }
      | .symbolic condition =>
          if inferSort condition != some .bool then none
          else
            let thenState := appendEffectfulHeapEvents conditionState [.thenBranchSelected]
            let elseState := appendEffectfulHeapEvents conditionState [.elseBranchSelected]
            match executeEffectfulConditionalBranch thenBranch thenState,
                executeEffectfulConditionalBranch elseBranch elseState with
            | some thenResult, some elseResult =>
                let thenValue := effectfulConditionalValueAtJoinedType thenResult joinedType
                let elseValue := effectfulConditionalValueAtJoinedType elseResult joinedType
                some {
                  paths := [{
                    guard := condition
                    value := thenValue
                    valueType := joinedType
                    state := thenResult.state
                  }, {
                    guard := .not condition
                    value := elseValue
                    valueType := joinedType
                    state := elseResult.state
                  }]
                  joinedValue := .ite condition thenValue elseValue
                  joinedType
                }
            | _, _ => none

def effectfulConditionalBranchPureValue : EffectfulConditionalBranch → Option Term
  | .boolean value => some (.boolLiteral value)
  | .integer value => some (.intLiteral value)
  | .unit => some .unitLiteral
  | .fieldAugAssign _ => none

/- An eager `ite` is available only for genuinely pure branches.  In particular it cannot erase
the state transition of an `AugAssign` branch. -/
def lowerEffectfulConditionalAsEagerIte
    (condition : Term) (thenBranch elseBranch : EffectfulConditionalBranch) : Option Term :=
  match effectfulConditionalBranchPureValue thenBranch,
      effectfulConditionalBranchPureValue elseBranch with
  | some thenValue, some elseValue =>
      if inferSort condition != some .bool then none
      else
        match joinHeapConditionalTypes
            (effectfulConditionalBranchType thenBranch)
            (effectfulConditionalBranchType elseBranch) .unavailable with
        | none => none
        | some joinedType =>
            let thenResult : EffectfulConditionalBranchResult := {
              value := thenValue
              valueType := effectfulConditionalBranchType thenBranch
              state := { heap := 0, mask := 0, fields := [], fullPermissions := [], trace := [] }
            }
            let elseResult : EffectfulConditionalBranchResult := {
              value := elseValue
              valueType := effectfulConditionalBranchType elseBranch
              state := { heap := 0, mask := 0, fields := [], fullPermissions := [], trace := [] }
            }
            some (.ite condition
              (effectfulConditionalValueAtJoinedType thenResult joinedType)
              (effectfulConditionalValueAtJoinedType elseResult joinedType))
  | _, _ => none

theorem field_augassign_without_full_permission_refuses
    (request : EffectfulFieldAugAssign) (state : EffectfulHeapExpressionState)
    (missing : hasFullEffectfulFieldPermission state request.receiver request.field = false) :
    executeEffectfulFieldAugAssign request state = none := by
  simp [executeEffectfulFieldAugAssign, missing]

theorem accepted_field_augassign_requires_full_permission
    (request : EffectfulFieldAugAssign) (state : EffectfulHeapExpressionState)
    (result : EffectfulFieldAugAssignResult)
    (accepted : executeEffectfulFieldAugAssign request state = some result) :
    hasFullEffectfulFieldPermission state request.receiver request.field = true := by
  cases permission : hasFullEffectfulFieldPermission state request.receiver request.field <;>
    simp_all [executeEffectfulFieldAugAssign]

theorem successful_field_augassign_has_python_evaluation_order
    (request : EffectfulFieldAugAssign) (state : EffectfulHeapExpressionState)
    (oldValue : Int)
    (receiverNamed : request.receiver.isEmpty = false)
    (fieldNamed : request.field.isEmpty = false)
    (permission : hasFullEffectfulFieldPermission state request.receiver request.field = true)
    (found : lookupEffectfulIntegerField state.fields request.receiver request.field =
      some oldValue) :
    let value := applyEffectfulIntegerAugOperator
      request.operator oldValue request.rightOperand
    executeEffectfulFieldAugAssign request state = some {
      value
      state := {
        state with
          heap := state.heap + 1
          fields := writeEffectfulIntegerField state.fields request.receiver request.field value
          trace := state.trace ++ [
            .receiverEvaluated request.receiver,
            .fieldRead request.receiver request.field oldValue,
            .rightOperandEvaluated request.rightOperand,
            .fieldWritten request.receiver request.field value
          ]
      }
    } := by
  simp [executeEffectfulFieldAugAssign, receiverNamed, fieldNamed, permission, found]

theorem successful_field_augassign_evaluates_receiver_once_and_reads_before_write
    (request : EffectfulFieldAugAssign) (state : EffectfulHeapExpressionState)
    (result : EffectfulFieldAugAssignResult) (oldValue : Int)
    (receiverNamed : request.receiver.isEmpty = false)
    (fieldNamed : request.field.isEmpty = false)
    (permission : hasFullEffectfulFieldPermission state request.receiver request.field = true)
    (found : lookupEffectfulIntegerField state.fields request.receiver request.field =
      some oldValue)
    (accepted : executeEffectfulFieldAugAssign request state = some result) :
    result.state.trace.drop state.trace.length = [
      .receiverEvaluated request.receiver,
      .fieldRead request.receiver request.field oldValue,
      .rightOperandEvaluated request.rightOperand,
      .fieldWritten request.receiver request.field result.value
    ] := by
  rw [successful_field_augassign_has_python_evaluation_order request state oldValue
    receiverNamed fieldNamed permission found] at accepted
  injection accepted with resultEq
  subst result
  simp

theorem successful_field_augassign_advances_heap_and_preserves_mask
    (request : EffectfulFieldAugAssign) (state : EffectfulHeapExpressionState)
    (result : EffectfulFieldAugAssignResult)
    (accepted : executeEffectfulFieldAugAssign request state = some result) :
    result.state.heap = state.heap + 1 ∧ result.state.mask = state.mask := by
  unfold executeEffectfulFieldAugAssign at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  next oldValue found =>
    injection accepted with resultEq
    subst result
    simp

theorem concrete_true_conditional_executes_only_then_branch
    (thenBranch elseBranch : EffectfulConditionalBranch)
    (state : EffectfulHeapExpressionState)
    (joinedType : HeapConditionalType)
    (thenResult : EffectfulConditionalBranchResult)
    (joined : joinHeapConditionalTypes
      (effectfulConditionalBranchType thenBranch)
      (effectfulConditionalBranchType elseBranch) .unavailable = some joinedType)
    (thenExecuted : executeEffectfulConditionalBranch thenBranch
      (appendEffectfulHeapEvents
        (appendEffectfulHeapEvents state [.conditionEvaluated]) [.thenBranchSelected]) =
      some thenResult) :
    executeEffectfulConditional (.concrete true) thenBranch elseBranch state = some {
      paths := [{
        guard := .boolLiteral true
        value := effectfulConditionalValueAtJoinedType thenResult joinedType
        valueType := joinedType
        state := thenResult.state
      }]
      joinedValue := effectfulConditionalValueAtJoinedType thenResult joinedType
      joinedType
    } := by
  simp [executeEffectfulConditional, joined, thenExecuted]

theorem concrete_false_conditional_executes_only_else_branch
    (thenBranch elseBranch : EffectfulConditionalBranch)
    (state : EffectfulHeapExpressionState)
    (joinedType : HeapConditionalType)
    (elseResult : EffectfulConditionalBranchResult)
    (joined : joinHeapConditionalTypes
      (effectfulConditionalBranchType thenBranch)
      (effectfulConditionalBranchType elseBranch) .unavailable = some joinedType)
    (elseExecuted : executeEffectfulConditionalBranch elseBranch
      (appendEffectfulHeapEvents
        (appendEffectfulHeapEvents state [.conditionEvaluated]) [.elseBranchSelected]) =
      some elseResult) :
    executeEffectfulConditional (.concrete false) thenBranch elseBranch state = some {
      paths := [{
        guard := .boolLiteral true
        value := effectfulConditionalValueAtJoinedType elseResult joinedType
        valueType := joinedType
        state := elseResult.state
      }]
      joinedValue := effectfulConditionalValueAtJoinedType elseResult joinedType
      joinedType
    } := by
  simp [executeEffectfulConditional, joined, elseExecuted]

theorem symbolic_effectful_conditional_keeps_branch_states_local
    (condition : Term) (thenBranch elseBranch : EffectfulConditionalBranch)
    (state : EffectfulHeapExpressionState)
    (joinedType : HeapConditionalType)
    (thenResult elseResult : EffectfulConditionalBranchResult)
    (typed : (inferSort condition != some .bool) = false)
    (joined : joinHeapConditionalTypes
      (effectfulConditionalBranchType thenBranch)
      (effectfulConditionalBranchType elseBranch) .unavailable = some joinedType)
    (thenExecuted : executeEffectfulConditionalBranch thenBranch
      (appendEffectfulHeapEvents
        (appendEffectfulHeapEvents state [.conditionEvaluated]) [.thenBranchSelected]) =
      some thenResult)
    (elseExecuted : executeEffectfulConditionalBranch elseBranch
      (appendEffectfulHeapEvents
        (appendEffectfulHeapEvents state [.conditionEvaluated]) [.elseBranchSelected]) =
      some elseResult) :
    executeEffectfulConditional (.symbolic condition) thenBranch elseBranch state = some {
      paths := [{
        guard := condition
        value := effectfulConditionalValueAtJoinedType thenResult joinedType
        valueType := joinedType
        state := thenResult.state
      }, {
        guard := .not condition
        value := effectfulConditionalValueAtJoinedType elseResult joinedType
        valueType := joinedType
        state := elseResult.state
      }]
      joinedValue := .ite condition
        (effectfulConditionalValueAtJoinedType thenResult joinedType)
        (effectfulConditionalValueAtJoinedType elseResult joinedType)
      joinedType
    } := by
  simp [executeEffectfulConditional, joined, typed, thenExecuted, elseExecuted]

theorem incompatible_effectful_conditional_result_types_refuse
    (decision : EffectfulConditionalDecision)
    (thenBranch elseBranch : EffectfulConditionalBranch)
    (state : EffectfulHeapExpressionState)
    (incompatible : joinHeapConditionalTypes
      (effectfulConditionalBranchType thenBranch)
      (effectfulConditionalBranchType elseBranch) .unavailable = none) :
    executeEffectfulConditional decision thenBranch elseBranch state = none := by
  simp [executeEffectfulConditional, incompatible]

theorem boolean_integer_effectful_conditional_results_join_as_integer :
    joinHeapConditionalTypes
      (effectfulConditionalBranchType (.boolean true))
      (effectfulConditionalBranchType (.integer 7)) .unavailable =
      some (.scalar .int) := by
  rfl

theorem eager_ite_refuses_effectful_then_branch
    (condition : Term) (request : EffectfulFieldAugAssign)
    (elseBranch : EffectfulConditionalBranch) :
    lowerEffectfulConditionalAsEagerIte condition (.fieldAugAssign request) elseBranch = none := by
  rfl

theorem eager_ite_refuses_effectful_else_branch
    (condition : Term) (request : EffectfulFieldAugAssign)
    (thenBranch : EffectfulConditionalBranch) :
    lowerEffectfulConditionalAsEagerIte condition thenBranch (.fieldAugAssign request) = none := by
  cases thenBranch <;> rfl

end Maledictus
