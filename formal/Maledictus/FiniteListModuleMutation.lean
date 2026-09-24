namespace Maledictus.FiniteListModuleMutation

/-!
# Finite primitive-list module mutation model

This is an executable algebraic model of the deliberately narrow Python
module-initialization operation accepted by the scalar frontend.  It records
Python's augmented-assignment evaluation order explicitly: evaluate the
container, evaluate the index once, read the old element, evaluate the right
operand, apply the primitive integer operator, then store.

This file proves properties of the model.  It is not a proof that the Rust
frontend implements the model; no extraction or correspondence theorem is
claimed here.
-/

inductive PrimitiveIntOperator where
  | add
  | subtract
  | multiply
  deriving DecidableEq, Repr

def PrimitiveIntOperator.apply : PrimitiveIntOperator -> Int -> Int -> Int
  | .add, left, right => left + right
  | .subtract, left, right => left - right
  | .multiply, left, right => left * right

inductive EvaluationStep where
  | container
  | index
  | read
  | rightHandSide
  | primitiveOperation
  | store
  deriving DecidableEq, Repr

def pythonEvaluationOrder : List EvaluationStep :=
  [ .container, .index, .read, .rightHandSide, .primitiveOperation, .store ]

structure Request where
  values : List Int
  index : Nat
  operator : PrimitiveIntOperator
  right : Int

structure Result where
  values : List Int
  previous : Int
  right : Int
  value : Int
  trace : List EvaluationStep

/-- Execute only when the static natural index is in bounds. -/
def execute (request : Request) : Option Result :=
  match request.values[request.index]? with
  | none => none
  | some previous =>
      let value := request.operator.apply previous request.right
      some {
        values := request.values.set request.index value
        previous := previous
        right := request.right
        value := value
        trace := pythonEvaluationOrder
      }

theorem execute_refuses_out_of_bounds
    (request : Request) (outOfBounds : request.values.length <= request.index) :
    execute request = none := by
  simp [execute, List.getElem?_eq_none outOfBounds]

theorem execute_success_records_exact_evaluation_order
    (request : Request) (result : Result)
    (success : execute request = some result) :
    result.trace = pythonEvaluationOrder := by
  unfold execute at success
  split at success
  next => contradiction
  next =>
    cases success
    rfl

theorem execute_success_preserves_length
    (request : Request) (result : Result)
    (success : execute request = some result) :
    result.values.length = request.values.length := by
  unfold execute at success
  split at success
  next => contradiction
  next =>
    cases success
    simp

theorem execute_success_records_right_operand_once
    (request : Request) (result : Result)
    (success : execute request = some result) :
    result.right = request.right := by
  unfold execute at success
  split at success
  next => contradiction
  next =>
    cases success
    rfl

theorem execute_success_uses_primitive_operator
    (request : Request) (result : Result)
    (success : execute request = some result) :
    result.value = request.operator.apply result.previous request.right := by
  unfold execute at success
  split at success
  next => contradiction
  next =>
    cases success
    rfl

theorem execute_success_updates_target_index
    (request : Request) (result : Result)
    (success : execute request = some result) :
    result.values[request.index]? = some result.value := by
  unfold execute at success
  split at success
  next => contradiction
  next previous lookup =>
    have inBounds : request.index < request.values.length :=
      (List.getElem?_eq_some_iff.mp lookup).1
    cases success
    exact List.getElem?_set_self inBounds

theorem execute_success_preserves_distinct_indices
    (request : Request) (result : Result)
    (success : execute request = some result)
    (other : Nat) (distinct : other ≠ request.index) :
    result.values[other]? = request.values[other]? := by
  unfold execute at success
  split at success
  next => contradiction
  next =>
    cases success
    exact List.getElem?_set_ne distinct.symm

theorem execute_example_add :
    execute { values := [1], index := 0, operator := .add, right := 1 } =
      some {
        values := [2]
        previous := 1
        right := 1
        value := 2
        trace := pythonEvaluationOrder
      } := by
  rfl

end Maledictus.FiniteListModuleMutation
