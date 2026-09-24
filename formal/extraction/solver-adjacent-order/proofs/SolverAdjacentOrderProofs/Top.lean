import SolverAdjacentOrderProofs.Refinement

open Aeneas Aeneas.Std Result

namespace SolverAdjacentOrder.Proofs

noncomputable section

set_option maxHeartbeats 0
set_option allowUnsafeReducibility true

attribute [local reducible] Slice

abbrev emptyTermSlice : Slice vc.Term := ⟨[], by simp⟩

theorem lift_emptyTermSlice :
    lift (Array.to_slice (Std.Array.empty vc.Term)) = .ok emptyTermSlice := by
  rfl

theorem nonnegative_empty_exact (term : vc.Term) (binder : Str) :
    solver.is_nonnegative_bound term binder emptyTermSlice =
      nonnegativeBoundSpec term binder [] := by
  simpa [emptyTermSlice] using
    is_nonnegative_bound_all_inputs_exact term binder emptyTermSlice

theorem adjacent_empty_exact (term : vc.Term) (binder : Str) (sorted : vc.Term) :
    solver.is_adjacent_upper_bound term binder sorted emptyTermSlice =
      adjacentBoundSpec term binder sorted [] := by
  simpa [emptyTermSlice] using
    is_adjacent_upper_bound_all_inputs_exact term binder sorted emptyTermSlice

def adjacentGuardSpec (guard : vc.Term) (binder : Str) (sorted : vc.Term) :
    Result Bool := do
  let normalized <- unwrapSingletonAndSpec guard
  match normalized with
  | .IfThenElse condition thenValue elseValue => do
      let condition <- unwrapSingletonAndSpec condition
      let thenValue <- unwrapSingletonAndSpec thenValue
      let elseValue <- unwrapSingletonAndSpec elseValue
      if !(condition == elseValue) then
        .ok false
      else
        let remaining <- lift (Array.to_slice (Std.Array.empty vc.Term))
        let nonnegative <- nonnegativeBoundSpec condition binder remaining.val
        if nonnegative then
          let remaining <- lift (Array.to_slice (Std.Array.empty vc.Term))
          adjacentBoundSpec thenValue binder sorted remaining.val
        else
          .ok false
  | .And values => do
      let first <- core.slice.Slice.split_first (ModelVec.deref values)
      match first with
      | none => .ok false
      | some (head, tail) => do
          let nonnegative <- nonnegativeBoundSpec head binder tail.val
          if nonnegative then adjacentBoundSpec head binder sorted tail.val else .ok false
  | term => do
      let remaining <- lift (Array.to_slice (Std.Array.empty vc.Term))
      let nonnegative <- nonnegativeBoundSpec term binder remaining.val
      if nonnegative then
        let remaining <- lift (Array.to_slice (Std.Array.empty vc.Term))
        adjacentBoundSpec term binder sorted remaining.val
      else
        .ok false

def exactSortedAdjacentOrderSpec (term : vc.Term) : Result Bool :=
  match term with
  | .ForAll binder .Int body => do
      let body <- unwrapSingletonAndSpec body
      match body with
      | .Implies guard right => do
          let right <- unwrapSingletonAndSpec right
          match right with
          | .LessEqual (.ListGet currentList currentIndex) (.ListGet nextList nextIndex) =>
              if !(currentList == nextList) then
                .ok false
              else
                match currentList with
                | .ListSorted _ => do
                    let binder <-
                      alloc.string.String.Insts.CoreOpsDerefDerefStr.deref binder
                    let currentMatches <- pythonIndexSpec currentIndex binder currentList false
                    if !currentMatches then
                      .ok false
                    else
                      let nextMatches <- pythonIndexSpec nextIndex binder currentList true
                      if nextMatches then adjacentGuardSpec guard binder currentList else .ok false
                | _ => .ok false
          | _ => .ok false
      | _ => .ok false
  | _ => .ok false

theorem is_exact_sorted_adjacent_order_theorem_all_inputs_exact (term : vc.Term) :
    solver.is_exact_sorted_adjacent_order_theorem term =
      exactSortedAdjacentOrderSpec term := by
  unfold solver.is_exact_sorted_adjacent_order_theorem exactSortedAdjacentOrderSpec
  cases term <;> try rfl
  case ForAll binder sort body =>
    cases sort <;> try rfl
    simp only [bind_tc_ok]
    rw [unwrap_singleton_and_all_inputs_exact]
    cases bodyResult : unwrapSingletonAndSpec body <;> try rfl
    case ok normalizedBody =>
      cases normalizedBody <;> try rfl
      case Implies guard right =>
        simp only [bind_tc_ok]
        rw [unwrap_singleton_and_all_inputs_exact]
        cases rightResult : unwrapSingletonAndSpec right <;> try rfl
        case ok normalizedRight =>
          cases normalizedRight <;> try rfl
          case LessEqual left right =>
            simp only [Box.Insts.CoreConvertAsRef.as_ref, bind_tc_ok]
            cases left <;> try rfl
            case ListGet currentList currentIndex =>
              cases right <;> try rfl
              case ListGet nextList nextIndex =>
                simp only [core.cmp.impls.PartialEqShared.ne,
                  alloc.boxed.PartialEqBox.eq,
                  core.cmp.PartialEq.ne.trait_default,
                  core.cmp.PartialEq.ne.default,
                  vc.Term.Insts.CoreCmpPartialEqTerm.eq, bind_tc_ok]
                cases equality : (currentList == nextList) <;>
                  simp only [equality, Bool.not_false, Bool.not_true, if_false, if_true,
                    bind_tc_ok]
                cases currentList <;>
                  try simp only [Box.Insts.CoreConvertAsRef.as_ref, bind_tc_ok] <;>
                  try rfl
                case ListSorted sortedValue =>
                  cases binderResult :
                    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref binder <;> try rfl
                  case ok binderSlice =>
                    simp only [Bool.false_eq_true, if_false, bind_tc_ok]
                    rw [is_python_index_of_all_inputs_exact]
                    cases currentResult :
                      pythonIndexSpec currentIndex binderSlice
                        (vc.Term.ListSorted sortedValue) false <;> try rfl
                    case ok currentMatches =>
                      cases currentMatches <;> try rfl
                      rw [is_python_index_of_all_inputs_exact]
                      cases nextResult :
                        pythonIndexSpec nextIndex binderSlice
                          (vc.Term.ListSorted sortedValue) true <;> try rfl
                      case ok nextMatches =>
                        cases nextMatches <;> try rfl
                        simp only [bind_tc_ok]
                        unfold adjacentGuardSpec
                        rw [unwrap_singleton_and_all_inputs_exact]
                        cases guardResult : unwrapSingletonAndSpec guard <;> try rfl
                        case ok normalizedGuard =>
                          cases normalizedGuard
                          case IfThenElse condition thenValue elseValue =>
                            simp only [bind_tc_ok]
                            rw [unwrap_singleton_and_all_inputs_exact]
                            cases conditionResult : unwrapSingletonAndSpec condition <;> try rfl
                            case ok normalizedCondition =>
                              simp only [bind_tc_ok]
                              rw [unwrap_singleton_and_all_inputs_exact]
                              cases thenResult : unwrapSingletonAndSpec thenValue <;> try rfl
                              case ok normalizedThen =>
                                simp only [bind_tc_ok]
                                rw [unwrap_singleton_and_all_inputs_exact]
                                cases elseResult : unwrapSingletonAndSpec elseValue <;> try rfl
                                case ok normalizedElse =>
                                  simp only [vc.Term.Insts.CoreCmpPartialEqTerm.eq, bind_tc_ok]
                                  cases conditionEquality :
                                    (normalizedCondition == normalizedElse)
                                  case false => simp
                                  case true =>
                                    simp only [Bool.not_true, Bool.false_eq_true, if_false,
                                      if_true, lift_emptyTermSlice, bind_tc_ok]
                                    rw [nonnegative_empty_exact]
                                    cases conditionBoundResult :
                                      nonnegativeBoundSpec normalizedCondition binderSlice [] <;>
                                      try rfl
                                    case ok nonnegative =>
                                      cases nonnegative <;> try rfl
                                      rw [adjacent_empty_exact]
                          case And values =>
                            simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true,
                              bind_tc_ok]
                            cases splitResult :
                              core.slice.Slice.split_first (ModelVec.deref values) <;>
                              try simp [splitResult] <;> try rfl
                            case ok firstAndTail =>
                              cases firstAndTail <;> try rfl
                              case some pair =>
                                rcases pair with ⟨first, remaining⟩
                                change (do
                                  let nonnegative ←
                                    solver.is_nonnegative_bound first binderSlice remaining
                                  if nonnegative = true then
                                    solver.is_adjacent_upper_bound first binderSlice
                                      (vc.Term.ListSorted sortedValue) remaining
                                  else
                                    .ok false) = _
                                rw [is_nonnegative_bound_all_inputs_exact]
                                cases remainingBoundResult :
                                  nonnegativeBoundSpec first binderSlice remaining.val
                                case fail error => simp [remainingBoundResult]
                                case div => simp [remainingBoundResult]
                                case ok nonnegative =>
                                  cases nonnegative
                                  case false => simp [remainingBoundResult]
                                  case true =>
                                    simp only [remainingBoundResult, bind_tc_ok, if_true]
                                    rw [is_adjacent_upper_bound_all_inputs_exact]
                          all_goals
                            simp only [lift_emptyTermSlice, bind_tc_ok]
                            rw [nonnegative_empty_exact]
                            cases genericBoundResult :
                              nonnegativeBoundSpec _ binderSlice [] <;> try rfl
                            case ok nonnegative =>
                              cases nonnegative <;> try rfl
                              rw [adjacent_empty_exact]
                              try simp
end

end SolverAdjacentOrder.Proofs
