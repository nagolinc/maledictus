-- Constructive external function models for the production Term::sort extraction.
import Aeneas
import VcTermSort.Code.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open VcTermSort

private def VcTermSort.ModelVec.asVec {T : Type}
    (values : VcTermSort.ModelVec T) : alloc.vec.Vec T :=
  ⟨values.take Usize.max, List.length_take_le _ _⟩

/-- Total loop runner used by the deterministic normalization of Aeneas's
    partial `loop` combinator. Every normalized loop advances one slice
    iterator exactly once per continuation, so the number of remaining
    elements plus the final exhausted check is sufficient. Reaching zero is
    retained as an explicit model failure rather than silently diverging. -/
def VcTermSort.runLoopFuel {State Output : Type} :
    Nat → (State → Result (ControlFlow State Output)) → State → Result Output
  | 0, _, _ => .fail .panic
  | fuel + 1, body, state => do
      let flow ← body state
      match flow with
      | ControlFlow.done output => .ok output
      | ControlFlow.cont next => runLoopFuel fuel body next

section
open Lean.Order

@[partial_fixpoint_monotone]
theorem VcTermSort.runLoopFuel_monotone
    {State Output : Type} {Φ : Sort _} [Lean.Order.PartialOrder Φ]
    (fuel : Nat) (body : Φ → State → Result (ControlFlow State Output))
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
            | ControlFlow.done output => Result.ok output
            | ControlFlow.cont next => runLoopFuel fuel (body parameter) next)) := by
        apply Lean.Order.monotone_bind
        · intro first second firstLeSecond
          exact monotone_apply state _ bodyMonotone first second firstLeSecond
        · intro first second firstLeSecond flow
          cases flow with
          | done output => exact FlatOrder.rel.refl
          | cont next => exact inductionHypothesis next first second firstLeSecond
      exact bound left right leftLeRight

private theorem VcTermSort.result_order_cases {T : Type}
    {left right : Result T} (ordered : left ⊑ right) :
    left = .div ∨ left = right := by
  change FlatOrder.rel left right at ordered
  cases ordered with
  | bot => exact Or.inl rfl
  | refl => exact Or.inr rfl

/-- The Aeneas partial loop is monotone in a monotone loop body.  Upstream
Aeneas does not currently register this higher-order rule, which prevents its
own raw mutually recursive extraction from elaborating when a loop body calls
another member of the mutual group.  This constructive fixpoint-induction
proof lets us retain and compile the actual raw program for the normalization
correspondence theorem. -/
private theorem VcTermSort.loop_body_monotone_function
    {State Output : Type} {Φ : Sort _} [Lean.Order.PartialOrder Φ]
    (body : Φ → State → Result (ControlFlow State Output))
    (bodyMonotone : Lean.Order.monotone body) :
    Lean.Order.monotone (fun parameter state => loop (body parameter) state) := by
  intro left right leftLeRight
  have bodyOrdered : ∀ state, body left state ⊑ body right state :=
    fun state => monotone_apply state body bodyMonotone left right leftLeRight
  apply loop.fixpoint_induct (body left)
    (motive := fun recur => ∀ state,
      recur state ⊑ loop (body right) state)
  · apply Lean.Order.admissible_pi
    intro state
    exact Lean.Order.admissible_apply
      (fun _ value => value ⊑ loop (body right) state) state
      (Lean.Order.admissible_flatOrder _ FlatOrder.rel.bot)
  · intro recur induction state
    simp only
    have stepOrdered := bodyOrdered state
    rcases VcTermSort.result_order_cases stepOrdered with leftDiverges | same
    · rw [leftDiverges]
      exact FlatOrder.rel.bot
    · rw [same]
      unfold loop
      cases observed : body right state with
      | fail error =>
          simp [observed]
          exact Lean.Order.PartialOrder.rel_refl
      | div =>
          simp [observed]
          exact Lean.Order.PartialOrder.rel_refl
      | ok flow =>
          cases flow with
          | done output =>
              simp [observed]
              exact Lean.Order.PartialOrder.rel_refl
          | cont next => simp [observed, induction next]

@[partial_fixpoint_monotone]
theorem VcTermSort.loop_body_monotone
    {State Output : Type} {Φ : Sort _} [Lean.Order.PartialOrder Φ]
    (body : Φ → State → Result (ControlFlow State Output))
    (bodyMonotone : Lean.Order.monotone body) (state : State) :
    Lean.Order.monotone (fun parameter => loop (body parameter) state) :=
  monotone_apply state _
    (VcTermSort.loop_body_monotone_function body bodyMonotone)

end

def VcTermSort.ModelVec.deref {T : Type}
    (values : VcTermSort.ModelVec T) : Slice T :=
  alloc.vec.Vec.deref values.asVec

def VcTermSort.ModelVec.len {T : Type}
    (values : VcTermSort.ModelVec T) : Usize :=
  alloc.vec.Vec.len values.asVec

theorem VcTermSort.ModelVec.deref_exact {T : Type}
    (values : VcTermSort.ModelVec T) (bounded : values.length ≤ Usize.max) :
    (VcTermSort.ModelVec.deref values).val = values := by
  change List.take Usize.max values = values
  exact (List.take_eq_self_iff values).mpr bounded

theorem VcTermSort.ModelVec.len_exact {T : Type}
    (values : VcTermSort.ModelVec T) (bounded : values.length ≤ Usize.max) :
    (VcTermSort.ModelVec.len values).val = values.length := by
  simp [VcTermSort.ModelVec.len, VcTermSort.ModelVec.asVec,
    (List.take_eq_self_iff values).mpr bounded]

def VcTermSort.ModelVec.with_capacity (T : Type) (_capacity : Usize) :
    VcTermSort.ModelVec T :=
  []

def VcTermSort.ModelVec.push {T : Type}
    (values : VcTermSort.ModelVec T) (value : T) :
    Result (VcTermSort.ModelVec T) := do
  let pushed ← alloc.vec.Vec.push values.asVec value
  .ok pushed.val

theorem VcTermSort.ModelVec.push_exact {T : Type}
    (values : VcTermSort.ModelVec T) (value : T)
    (bounded : values.length < Usize.max) :
    VcTermSort.ModelVec.push values value =
      .ok (List.append (show List T from values) [value]) := by
  unfold VcTermSort.ModelVec.push VcTermSort.ModelVec.asVec alloc.vec.Vec.push
  simp [(List.take_eq_self_iff values).mpr (Nat.le_of_lt bounded), bounded]

theorem VcTermSort.ModelVec.push_at_capacity_fails {T : Type}
    (values : VcTermSort.ModelVec T) (value : T)
    (full : values.length = Usize.max) :
    VcTermSort.ModelVec.push values value = .fail .maximumSizeExceeded := by
  have capacity_not_below_u32 : ¬ Usize.max < U32.max := by scalar_tac
  unfold VcTermSort.ModelVec.push VcTermSort.ModelVec.asVec alloc.vec.Vec.push
  simp [(List.take_eq_self_iff values).mpr (Nat.le_of_eq full), full,
    capacity_not_below_u32]

@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<&'1 @A, &'0 @B>}::gt"]
def Shared1A.Insts.CoreCmpPartialOrdShared0B.gt
    {A : Type} {B : Type} (inst : core.cmp.PartialOrd A B) :
    A → B → Result Bool := inst.gt

@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_tuple_field2_finish"]
def core.fmt.Formatter.debug_tuple_field2_finish :
    core.fmt.Formatter → Str → Dyn (fun type => core.fmt.Debug type) →
      Dyn (fun type => core.fmt.Debug type) →
      Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun formatter _ _ _ => .ok (.Ok (), formatter)

@[rust_fun "core::fmt::{core::fmt::Display<&'0 @T>}::fmt"]
def Shared0T.Insts.CoreFmtDisplay.fmt
    {T : Type} (inst : core.fmt.Display T) :
    T → core.fmt.Formatter →
      Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  inst.fmt

@[rust_fun "core::fmt::{core::fmt::Display<str>}::fmt"]
def Str.Insts.CoreFmtDisplay.fmt :
    Str → core.fmt.Formatter →
      Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ formatter => .ok (.Ok (), formatter)

@[rust_fun "core::hint::must_use"]
def core.hint.must_use {T : Type} (value : T) : Result T := .ok value

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or_else"]
def core.option.Option.ok_or_else
    {T : Type} {E : Type} {F : Type}
    (inst : core.ops.function.FnOnce F Unit E) :
    Option T → F → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, fallback => do
      let error ← inst.call_once fallback ()
      .ok (.Err error)

@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
    {T : Type} {E : Type} : Option T → E → Result (core.result.Result T E)
  | some value, _ => .ok (.Ok value)
  | none, error => .ok (.Err error)

@[rust_fun "core::option::{core::option::Option<&'0 @T>}::cloned"]
def core.option.OptionShared0T.cloned
    {T : Type} (inst : core.clone.Clone T) :
    Option T → Result (Option T)
  | none => .ok none
  | some value => do
      let cloned ← inst.clone value
      .ok (some cloned)

@[rust_fun "alloc::boxed::{core::cmp::PartialEq<Box<@T>, Box<@T>>}::ne"]
def Box.Insts.CoreCmpPartialEqBox.ne
    {T : Type} (_A : Type) (inst : core.cmp.PartialEq T T) :
    T → T → Result Bool := inst.ne

@[rust_fun "alloc::boxed::{core::fmt::Debug<Box<@T>>}::fmt"]
def Box.Insts.CoreFmtDebug.fmt
    {T : Type} (_A : Type) (inst : core.fmt.Debug T) :
    T → core.fmt.Formatter →
      Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  inst.fmt

@[rust_fun "alloc::boxed::{core::convert::AsRef<Box<@T>, @T>}::as_ref"]
def Box.Insts.CoreConvertAsRef.as_ref
    {T : Type} (_A : Type) (value : T) : Result T := .ok value

@[rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, alloc::alloc::Global>}::new"]
def alloc.collections.btree.set.BTreeSetTGlobal.new
    (T : Type) : Result (alloc.collections.btree.set.BTreeSet T Global) :=
  .ok []

@[rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, @A>}::insert"]
def alloc.collections.btree.set.BTreeSet.insert
    {T : Type} {A : Type} (_cloneAllocator : core.clone.Clone A)
    (ord : core.cmp.Ord T)
    (values : alloc.collections.btree.set.BTreeSet T A) (value : T) :
    Result (Bool × alloc.collections.btree.set.BTreeSet T A) := do
  let present ← List.anyM (fun existing => ord.eqInst.partialEqInst.eq existing value) values
  .ok (!present, if present then values else value :: values)

/-- Aeneas currently erases `core::fmt::Arguments` to `Unit`, so exact formatted
    error text is an explicit open correspondence obligation. This total model
    is sufficient to expose and compile every control-flow branch. -/
@[rust_fun "alloc::fmt::format"]
def alloc.fmt.format (_ : core.fmt.Arguments) : Result String := .ok ""

private def stringOfAsciiBytes (value : Str) : String :=
  String.ofList (value.val.map (fun byte => Char.ofNat byte.val))

@[rust_fun
  "alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned"]
def Str.Insts.AllocBorrowToOwnedString.to_owned (value : Str) : Result String :=
  .ok (stringOfAsciiBytes value)

@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqString.eq
    (left right : String) : Result Bool := .ok (left == right)

@[rust_fun
  "alloc::string::{core::cmp::PartialOrd<alloc::string::String, alloc::string::String>}::partial_cmp"]
def alloc.string.String.Insts.CoreCmpPartialOrdString.partial_cmp
    (left right : String) : Result (Option Ordering) :=
  .ok (some (compare left right))

@[rust_fun "alloc::string::{core::cmp::Ord<alloc::string::String>}::cmp"]
def alloc.string.String.Insts.CoreCmpOrd.cmp
    (left right : String) : Result Ordering := .ok (compare left right)

@[rust_fun "alloc::string::{alloc::string::String}::is_empty"]
def alloc.string.String.is_empty (value : String) : Result Bool :=
  .ok value.isEmpty

@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone
    (value : String) : Result String := .ok value

@[rust_fun "alloc::string::{core::fmt::Debug<alloc::string::String>}::fmt"]
def alloc.string.String.Insts.CoreFmtDebug.fmt :
    String → core.fmt.Formatter →
      Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ formatter => .ok (.Ok (), formatter)

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
def VcTermSort.ModelVec.is_empty
    {T : Type} (_A : Type) (values : VcTermSort.ModelVec T) : Result Bool :=
  .ok values.isEmpty

@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    {T : Type} (_A : Type) (values : VcTermSort.ModelVec T) :
    Result (core.slice.iter.Iter T) :=
  .ok ⟨values.deref, 0⟩

/-- Exact constructive model of the source-derived `Clone` implementation for
    immutable `Sort` values. Rust's derived clone is observationally the same
    value; Lean values are immutable, so identity is the complete extensional
    model and does not need a second recursive traversal. -/
def Sort.Insts.CoreCloneClone.clone (sort : «Sort») : Result «Sort» :=
  .ok sort

/-- `Debug` affects only diagnostic text in this extracted closure. Aeneas
    erases the formatter state, so the constructive model preserves it and
    records exact formatted-error correspondence as an open obligation. -/
def Sort.Insts.CoreFmtDebug.fmt :
    «Sort» → core.fmt.Formatter →
      Result ((core.result.Result _root_.Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ formatter => .ok (.Ok (), formatter)

mutual

/-- Structural equality for the constructive `Sort` model. -/
def sortModelEq : «Sort» → «Sort» → _root_.Bool
  | .Bool, .Bool
  | .Int, .Int
  | .Float, .Float
  | .String, .String
  | .Unit, .Unit
  | .Reference, .Reference
  | .Class, .Class
  | .Bytes, .Bytes
  | .Range, .Range => true
  | .Tuple left, .Tuple right => sortModelListEq left right
  | .List left, .List right
  | .VariadicTuple left, .VariadicTuple right
  | .Set left, .Set right
  | .DictKeys left, .DictKeys right => sortModelEq left right
  | .Dict leftKey leftValue, .Dict rightKey rightValue
  | .FiniteDict leftKey leftValue, .FiniteDict rightKey rightValue =>
      sortModelEq leftKey rightKey && sortModelEq leftValue rightValue
  | _, _ => false

def sortModelListEq : List «Sort» → List «Sort» → _root_.Bool
  | [], [] => true
  | left :: leftTail, right :: rightTail =>
      sortModelEq left right && sortModelListEq leftTail rightTail
  | _, _ => false

end

/-- Public proof-facing views of the mutually recursive structural equality
    functions. Keeping the operational definitions mutually grouped lets Lean
    accept their nested recursion while these wrappers provide stable theorem
    names outside this generated external-model module. -/
def VcTermSort.sortModelEqPublic (left right : «Sort») : _root_.Bool :=
  sortModelEq left right

def VcTermSort.sortModelListEqPublic (left right : List «Sort») : _root_.Bool :=
  sortModelListEq left right

/-- Exact constructive model of the source-derived `PartialEq` implementation
    for `Sort`. -/
def Sort.Insts.CoreCmpPartialEqSort.eq
    (left right : «Sort») : Result _root_.Bool :=
  .ok (VcTermSort.sortModelEqPublic left right)

theorem VcTermSort.sortPartialEqModel
    (left right : «Sort») :
    Sort.Insts.CoreCmpPartialEqSort.eq left right =
      .ok (VcTermSort.sortModelEqPublic left right) := by
  rfl
