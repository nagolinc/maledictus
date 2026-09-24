import SolverAdjacentOrder

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section

namespace SolverAdjacentOrder.Proofs

def integerLiteralSpec : vc.Term -> Std.I64 -> Bool
  | .Int value, expected => value = expected
  | _, _ => false

def stringEqSpec (left : String) (right : Str) : Result Bool :=
  .ok (stringBytes left == right.val)

def boundVariableSpec : vc.Term -> Str -> Result Bool
  | .Variable variableName sort, binder =>
      match sort with
      | .Int => stringEqSpec variableName binder
      | _ => .ok false
  | _, _ => .ok false

def boundSuccessorSpec : vc.Term -> Str -> Result Bool
  | .Add left right, binder => do
      let leftBound <- boundVariableSpec left binder
      if leftBound then
        .ok (integerLiteralSpec right 1#i64)
      else
        let leftOne := integerLiteralSpec left 1#i64
        if leftOne then boundVariableSpec right binder else .ok false
  | _, _ => .ok false

theorem is_integer_literal_all_inputs_exact (term : vc.Term) (expected : Std.I64) :
    solver.is_integer_literal term expected = .ok (integerLiteralSpec term expected) := by
  cases term <;> simp [solver.is_integer_literal, integerLiteralSpec]

theorem is_bound_variable_all_inputs_exact (term : vc.Term) (binder : Str) :
    solver.is_bound_variable term binder = boundVariableSpec term binder := by
  cases term <;> simp [solver.is_bound_variable, boundVariableSpec]
  case Variable variableName sort =>
    cases sort <;> simp [solver.is_bound_variable, boundVariableSpec, stringEqSpec,
      alloc.string.String.Insts.CoreCmpPartialEqStr.eq]

theorem is_bound_successor_all_inputs_exact (term : vc.Term) (binder : Str) :
    solver.is_bound_successor term binder = boundSuccessorSpec term binder := by
  cases term <;> try rfl
  case Add left right =>
    simp only [solver.is_bound_successor, boundSuccessorSpec]
    rw [is_bound_variable_all_inputs_exact, is_integer_literal_all_inputs_exact]
    cases boundVariableSpec left binder <;> simp_all
    case ok leftBound =>
      cases leftBound <;> simp [is_integer_literal_all_inputs_exact,
        is_bound_variable_all_inputs_exact]

def nonnegativeOneSpec (term : vc.Term) (binder : Str) : Result Bool :=
  match term with
  | .GreaterEqual left right => do
      let bound <- boundVariableSpec left binder
      if bound then .ok (integerLiteralSpec right 0#i64) else .ok false
  | .LessEqual left right =>
      if integerLiteralSpec left 0#i64 then boundVariableSpec right binder else .ok false
  | _ => .ok false

def nonnegativeBoundSpec : vc.Term -> Str -> List vc.Term -> Result Bool
  | term, binder, [] => nonnegativeOneSpec term binder
  | term, binder, next :: tail => do
      let matched <- nonnegativeOneSpec term binder
      if matched then .ok true else nonnegativeBoundSpec next binder tail

theorem result_bool_identity (result : Result Bool) :
    (do
      let value <- result
      if value then .ok true else .ok false) = result := by
  cases result <;> simp_all
  case ok value => cases value <;> rfl

theorem is_nonnegative_bound_all_inputs_exact
    (term : vc.Term) (binder : Str) (remaining : Slice vc.Term) :
    solver.is_nonnegative_bound term binder remaining =
      nonnegativeBoundSpec term binder remaining.val := by
  rcases remaining with ⟨remaining, bounded⟩
  induction remaining generalizing term with
  | nil =>
      rw [solver.is_nonnegative_bound.eq_def]
      cases term <;> simp [nonnegativeBoundSpec, nonnegativeOneSpec,
        core.slice.Slice.split_first, is_integer_literal_all_inputs_exact,
        is_bound_variable_all_inputs_exact, result_bool_identity]
  | cons next tail inductionHypothesis =>
      rw [solver.is_nonnegative_bound.eq_def]
      cases term <;> simp [nonnegativeBoundSpec, nonnegativeOneSpec,
        core.slice.Slice.split_first, is_integer_literal_all_inputs_exact,
        is_bound_variable_all_inputs_exact, result_bool_identity, inductionHypothesis]

def adjacentOneSpec (term : vc.Term) (binder : Str) (sorted : vc.Term) : Result Bool :=
  match term with
  | .Less left right => do
      let successor <- boundSuccessorSpec left binder
      if successor then
        match right with
        | .ListLength value => .ok (value == sorted)
        | _ => .ok false
      else
        .ok false
  | _ => .ok false

def adjacentBoundSpec : vc.Term -> Str -> vc.Term -> List vc.Term -> Result Bool
  | term, binder, sorted, [] => adjacentOneSpec term binder sorted
  | term, binder, sorted, next :: tail => do
      let matched <- adjacentOneSpec term binder sorted
      if matched then .ok true else adjacentBoundSpec next binder sorted tail

theorem is_adjacent_upper_bound_all_inputs_exact
    (term : vc.Term) (binder : Str) (sorted : vc.Term) (remaining : Slice vc.Term) :
    solver.is_adjacent_upper_bound term binder sorted remaining =
      adjacentBoundSpec term binder sorted remaining.val := by
  rcases remaining with ⟨remaining, bounded⟩
  induction remaining generalizing term with
  | nil =>
      rw [solver.is_adjacent_upper_bound.eq_def]
      cases term <;> simp [adjacentBoundSpec, adjacentOneSpec,
        core.slice.Slice.split_first, is_bound_successor_all_inputs_exact,
        Box.Insts.CoreConvertAsRef.as_ref, vc.Term.Insts.CoreCmpPartialEqTerm.eq,
        result_bool_identity]
      case Less left right => cases right <;> simp [adjacentOneSpec,
        is_bound_successor_all_inputs_exact, Box.Insts.CoreConvertAsRef.as_ref,
        vc.Term.Insts.CoreCmpPartialEqTerm.eq]
  | cons next tail inductionHypothesis =>
      rw [solver.is_adjacent_upper_bound.eq_def]
      cases term <;> simp [adjacentBoundSpec, adjacentOneSpec,
        core.slice.Slice.split_first, is_bound_successor_all_inputs_exact,
        Box.Insts.CoreConvertAsRef.as_ref, vc.Term.Insts.CoreCmpPartialEqTerm.eq,
        result_bool_identity, inductionHypothesis]
      case Less left right => cases right <;> simp [adjacentBoundSpec, adjacentOneSpec,
        is_bound_successor_all_inputs_exact, Box.Insts.CoreConvertAsRef.as_ref,
        vc.Term.Insts.CoreCmpPartialEqTerm.eq, inductionHypothesis]

def unwrapFuelSpec : Nat -> vc.Term -> Result vc.Term
  | 0, _ => .fail .panic
  | fuel + 1, term =>
      match term with
      | .And [next] => unwrapFuelSpec fuel next
      | _ => .ok term

def unwrapSingletonAndSpec (term : vc.Term) : Result vc.Term :=
  unwrapFuelSpec (sizeOf term + 1) term

theorem unwrap_loop_fuel_exact (fuel : Nat) (term : vc.Term) :
    runLoopFuel fuel solver.unwrap_singleton_and_loop.body term =
      unwrapFuelSpec fuel term := by
  induction fuel generalizing term with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      cases term <;> try rfl
      case And values =>
        cases values with
        | nil =>
            simp [runLoopFuel, solver.unwrap_singleton_and_loop.body,
              unwrapFuelSpec, ModelVec.len, ModelVec.asVec]
        | cons first tail =>
            cases tail with
            | nil =>
                have maxPositive : Usize.max ≠ 0 := by scalar_tac
                simp [runLoopFuel, solver.unwrap_singleton_and_loop.body,
                  unwrapFuelSpec, ModelVec.len, ModelVec.index, ModelVec.asVec,
                  alloc.vec.Vec.index_usize, maxPositive, inductionHypothesis]
            | cons second rest =>
                have maxAboveOne : 1 < Usize.max := by scalar_tac
                have lengthNotOne : min Usize.max (rest.length + 1 + 1) ≠ 1 := by
                  omega
                simp [runLoopFuel, solver.unwrap_singleton_and_loop.body,
                  unwrapFuelSpec, ModelVec.len, ModelVec.asVec, lengthNotOne]

theorem unwrap_singleton_and_all_inputs_exact (term : vc.Term) :
    solver.unwrap_singleton_and term = unwrapSingletonAndSpec term := by
  unfold solver.unwrap_singleton_and unwrapSingletonAndSpec
  exact unwrap_loop_fuel_exact _ _

def pythonIndexSpec
    (term : vc.Term) (binder : Str) (sorted : vc.Term) (successor : Bool) :
    Result Bool := do
  let raw <- if successor then boundSuccessorSpec term binder
    else boundVariableSpec term binder
  if raw then
    .ok true
  else
    match term with
    | .IfThenElse condition thenValue elseValue => do
        let normalized <- unwrapSingletonAndSpec condition
        match normalized with
        | .Less left right => do
            let rawLeft <- if successor then boundSuccessorSpec left binder
              else boundVariableSpec left binder
            if !rawLeft || !integerLiteralSpec right 0#i64 then
              .ok false
            else
              let elseMatches <- if successor then boundSuccessorSpec elseValue binder
                else boundVariableSpec elseValue binder
              if !elseMatches then
                .ok false
              else
                match thenValue with
                | .Add (.ListLength value) offset =>
                    if value == sorted then
                      if successor then boundSuccessorSpec offset binder
                        else boundVariableSpec offset binder
                    else
                      .ok false
                | _ => .ok false
        | _ => .ok false
    | _ => .ok false

theorem is_python_index_of_all_inputs_exact
    (term : vc.Term) (binder : Str) (sorted : vc.Term) (successor : Bool) :
    solver.is_python_index_of term binder sorted successor =
      pythonIndexSpec term binder sorted successor := by
  unfold solver.is_python_index_of pythonIndexSpec
  cases successor with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [is_bound_variable_all_inputs_exact]
    cases boundVariableSpec term binder <;> simp_all
    case ok raw =>
      cases raw <;> simp_all
      cases term <;> simp_all
      case IfThenElse condition thenValue elseValue =>
        rw [unwrap_singleton_and_all_inputs_exact]
        cases unwrapSingletonAndSpec condition <;> simp_all
        case ok normalized =>
          cases normalized <;> simp_all
          case Less left right =>
            rw [is_bound_variable_all_inputs_exact]
            cases boundVariableSpec left binder <;> simp_all
            case ok rawLeft =>
              cases rawLeft <;> simp_all [is_integer_literal_all_inputs_exact]
              cases integerLiteralSpec right 0#i64 <;> simp_all
              rw [is_bound_variable_all_inputs_exact]
              cases boundVariableSpec elseValue binder <;> simp_all
              case ok elseMatches =>
                cases elseMatches <;> simp_all
                cases thenValue <;> simp only [Box.Insts.CoreConvertAsRef.as_ref,
                  bind_tc_ok]
                case Add length offset =>
                  cases length
                  case ListLength value =>
                    cases equality : (value == sorted) <;> simp [equality,
                      core.cmp.PartialEq.ne.default,
                      vc.Term.Insts.CoreCmpPartialEqTerm.eq,
                      is_bound_variable_all_inputs_exact]
                  all_goals simp only [Box.Insts.CoreConvertAsRef.as_ref, bind_tc_ok]
  | true =>
    simp only [if_true]
    rw [is_bound_successor_all_inputs_exact]
    cases boundSuccessorSpec term binder <;> simp_all
    case ok raw =>
      cases raw <;> simp_all
      cases term <;> simp_all
      case IfThenElse condition thenValue elseValue =>
        rw [unwrap_singleton_and_all_inputs_exact]
        cases unwrapSingletonAndSpec condition <;> simp_all
        case ok normalized =>
          cases normalized <;> simp_all
          case Less left right =>
            rw [is_bound_successor_all_inputs_exact]
            cases boundSuccessorSpec left binder <;> simp_all
            case ok rawLeft =>
              cases rawLeft <;> simp_all [is_integer_literal_all_inputs_exact]
              cases integerLiteralSpec right 0#i64 <;> simp_all
              rw [is_bound_successor_all_inputs_exact]
              cases boundSuccessorSpec elseValue binder <;> simp_all
              case ok elseMatches =>
                cases elseMatches <;> simp_all
                cases thenValue <;> simp only [Box.Insts.CoreConvertAsRef.as_ref,
                  bind_tc_ok]
                case Add length offset =>
                  cases length
                  case ListLength value =>
                    cases equality : (value == sorted) <;> simp [equality,
                      core.cmp.PartialEq.ne.default,
                      vc.Term.Insts.CoreCmpPartialEqTerm.eq,
                      is_bound_successor_all_inputs_exact]
                  all_goals simp only [Box.Insts.CoreConvertAsRef.as_ref, bind_tc_ok]

/-
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
                cases equality : (currentList == nextList) <;> simp_all [equality,
                  core.cmp.PartialEq.ne.default,
                  vc.Term.Insts.CoreCmpPartialEqTerm.eq]
                cases currentList <;> simp_all [Box.Insts.CoreConvertAsRef.as_ref]
                case ListSorted sortedValue =>
                  cases alloc.string.String.Insts.CoreOpsDerefDerefStr.deref binder <;>
                    simp_all
                  case ok binderSlice =>
                    rw [is_python_index_of_all_inputs_exact]
                    cases pythonIndexSpec currentIndex binderSlice (vc.Term.ListSorted sortedValue) false <;>
                      simp_all
                    case ok currentMatches =>
                      cases currentMatches <;> simp_all
                      rw [is_python_index_of_all_inputs_exact]
                      cases pythonIndexSpec nextIndex binderSlice (vc.Term.ListSorted sortedValue) true <;>
                        simp_all
                      case ok nextMatches =>
                        cases nextMatches <;> simp_all
                        unfold adjacentGuardSpec
                        rw [unwrap_singleton_and_all_inputs_exact]
                        cases unwrapSingletonAndSpec guard <;> simp_all
                        case ok normalizedGuard =>
                          cases normalizedGuard <;> simp_all
                          case IfThenElse condition thenValue elseValue =>
                            rw [unwrap_singleton_and_all_inputs_exact]
                            cases unwrapSingletonAndSpec condition <;> simp_all
                            case ok normalizedCondition =>
                              rw [unwrap_singleton_and_all_inputs_exact]
                              cases unwrapSingletonAndSpec thenValue <;> simp_all
                              case ok normalizedThen =>
                                rw [unwrap_singleton_and_all_inputs_exact]
                                cases unwrapSingletonAndSpec elseValue <;> simp_all
                                case ok normalizedElse =>
                                  cases conditionEquality : (normalizedCondition == normalizedElse) <;>
                                    simp_all [conditionEquality,
                                      vc.Term.Insts.CoreCmpPartialEqTerm.eq]
                                  rw [is_nonnegative_bound_all_inputs_exact]
                                  cases nonnegativeBoundSpec normalizedCondition binderSlice [] <;> simp_all
                                  case ok nonnegative =>
                                    cases nonnegative <;> simp_all
                                    rw [is_adjacent_upper_bound_all_inputs_exact]
                          case And values =>
                            rw [is_nonnegative_bound_all_inputs_exact]
                            rw [is_adjacent_upper_bound_all_inputs_exact]
                          all_goals
                            rw [is_nonnegative_bound_all_inputs_exact]
                            cases nonnegativeBoundSpec normalizedGuard binderSlice [] <;> simp_all
                            case ok nonnegative =>
                              cases nonnegative <;> simp_all
                              rw [is_adjacent_upper_bound_all_inputs_exact]

-/

end SolverAdjacentOrder.Proofs
