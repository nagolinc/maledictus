import Aeneas
import SolverSortPredicates.Code.Types

open Aeneas Aeneas.Std Result ControlFlow Error

namespace SolverSortPredicates

def runLoopFuel {State Output : Type} :
    Nat -> (State -> Result (ControlFlow State Output)) -> State -> Result Output
  | 0, _, _ => .fail .panic
  | fuel + 1, body, state => do
      let flow <- body state
      match flow with
      | .done output => .ok output
      | .cont next => runLoopFuel fuel body next

section

open Lean.Order

@[partial_fixpoint_monotone]
theorem runLoopFuel_monotone
    {State Output : Type} {Phi : Sort _} [Lean.Order.PartialOrder Phi]
    (fuel : Nat) (body : Phi -> State -> Result (ControlFlow State Output))
    (bodyMonotone : Lean.Order.monotone body) (state : State) :
    Lean.Order.monotone (fun parameter => runLoopFuel fuel (body parameter) state) := by
  induction fuel generalizing state with
  | zero =>
      intro left right leftLeRight
      exact FlatOrder.rel.refl
  | succ fuel inductionHypothesis =>
      intro left right leftLeRight
      simp only [runLoopFuel]
      have bound : Lean.Order.monotone (fun parameter =>
          Bind.bind (body parameter state) (fun flow =>
            match flow with
            | .done output => Result.ok output
            | .cont next => runLoopFuel fuel (body parameter) next)) := by
        apply Lean.Order.monotone_bind
        · intro first second firstLeSecond
          exact monotone_apply state _ bodyMonotone first second firstLeSecond
        · intro first second firstLeSecond flow
          cases flow with
          | done output => exact FlatOrder.rel.refl
          | cont next => exact inductionHypothesis next first second firstLeSecond
      exact bound left right leftLeRight

end

private def modelVecAsVec {T : Type} (values : List T) : alloc.vec.Vec T :=
  ⟨values.take Usize.max, List.length_take_le _ _⟩

@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    {T : Type} (_allocator : Type) :
    List T -> Result (core.slice.iter.Iter T) :=
  fun values => .ok ⟨alloc.vec.Vec.deref (modelVecAsVec values), 0⟩

theorem shared_vec_into_iter_exact {T : Type} (allocator : Type) (values : List T) :
    SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter allocator values =
      .ok ⟨⟨values.take Usize.max, List.length_take_le _ _⟩, 0⟩ := by
  rfl

end SolverSortPredicates
