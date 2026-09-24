import Maledictus.StaticStringSlice

namespace Maledictus

/-!
# Symbolic finite-list slicing

This model gives successful nonzero static Python slices exact finite-list semantics for an
arbitrary element type under idealized infallible allocation. A successful slice allocates a
distinct list object, preserves every earlier heap object, and records the exact source indices
used to build the result. `none` deliberately covers both an invalid source allocation and the
zero-step `ValueError`; exact diagnostic outcomes belong to the eventual production refinement.

These are model theorems. They become implementation evidence only after the Rust frontend and VC
lowering are connected by a source-bound refinement proof.
-/

structure SymbolicListHeap (α : Type) where
  objects : List (List α)
  deriving DecidableEq, Repr

structure SymbolicListSliceResult (α : Type) where
  heap : SymbolicListHeap α
  allocation : Nat
  sourceIndices : List Nat
  deriving DecidableEq, Repr

def selectSymbolicListIndices
    (source : List α) (indices : List Nat)
    (bounded : ∀ index, index ∈ indices → index < source.length) : List α :=
  indices.attach.map fun entry =>
    source.get ⟨entry.1, bounded entry.1 entry.2⟩

def evaluateSymbolicListSlice
    (heap : SymbolicListHeap α) (sourceAllocation : Nat)
    (lower upper : Option Int) (step : StaticSliceStep) :
    Option (SymbolicListSliceResult α) :=
  match heap.objects[sourceAllocation]? with
  | none => none
  | some source =>
      match indicesEq : staticSliceIndices lower upper step source.length with
      | none => none
      | some indices =>
          let selected := selectSymbolicListIndices source indices fun index member =>
            every_static_slice_index_is_in_bounds lower upper step source.length index
              ⟨indices, indicesEq, member⟩
          some {
            heap := ⟨heap.objects ++ [selected]⟩
            allocation := heap.objects.length
            sourceIndices := indices
          }

theorem selected_symbolic_list_length
    (source : List α) (indices : List Nat)
    (bounded : ∀ index, index ∈ indices → index < source.length) :
    (selectSymbolicListIndices source indices bounded).length = indices.length := by
  simp [selectSymbolicListIndices]

theorem selected_symbolic_list_value_came_from_source
    (source : List α) (indices : List Nat)
    (bounded : ∀ index, index ∈ indices → index < source.length)
    (value : α) (member : value ∈ selectSymbolicListIndices source indices bounded) :
    value ∈ source := by
  simp only [selectSymbolicListIndices, List.mem_map] at member
  obtain ⟨entry, _, valueEq⟩ := member
  rw [← valueEq]
  exact List.get_mem source ⟨entry.1, bounded entry.1 entry.2⟩

theorem successful_symbolic_slice_uses_fresh_allocation
    (heap : SymbolicListHeap α) (sourceAllocation : Nat)
    (lower upper : Option Int) (step : StaticSliceStep)
    (result : SymbolicListSliceResult α)
    (evaluated : evaluateSymbolicListSlice heap sourceAllocation lower upper step = some result) :
    result.allocation = heap.objects.length ∧
      result.heap.objects.length = heap.objects.length + 1 := by
  unfold evaluateSymbolicListSlice at evaluated
  split at evaluated
  · contradiction
  · rename_i source sourceEq
    split at evaluated
    · contradiction
    · rename_i indices indicesEq
      dsimp at evaluated
      injection evaluated with resultEq
      subst result
      simp

theorem successful_symbolic_slice_preserves_existing_allocations
    (heap : SymbolicListHeap α) (sourceAllocation existing : Nat)
    (lower upper : Option Int) (step : StaticSliceStep)
    (result : SymbolicListSliceResult α)
    (evaluated : evaluateSymbolicListSlice heap sourceAllocation lower upper step = some result)
    (existingInBounds : existing < heap.objects.length) :
    result.heap.objects[existing]? = heap.objects[existing]? := by
  unfold evaluateSymbolicListSlice at evaluated
  split at evaluated
  · contradiction
  · rename_i source sourceEq
    split at evaluated
    · contradiction
    · rename_i indices indicesEq
      dsimp at evaluated
      injection evaluated with resultEq
      subst result
      simp [List.getElem?_append, existingInBounds]

theorem successful_symbolic_slice_allocation_is_distinct_from_every_existing_allocation
    (heap : SymbolicListHeap α) (sourceAllocation existing : Nat)
    (lower upper : Option Int) (step : StaticSliceStep)
    (result : SymbolicListSliceResult α)
    (evaluated : evaluateSymbolicListSlice heap sourceAllocation lower upper step = some result)
    (existingInBounds : existing < heap.objects.length) :
    result.allocation ≠ existing := by
  have fresh := successful_symbolic_slice_uses_fresh_allocation
    heap sourceAllocation lower upper step result evaluated
  omega

theorem successful_symbolic_slice_result_is_selected_source
    (heap : SymbolicListHeap α) (sourceAllocation : Nat)
    (lower upper : Option Int) (step : StaticSliceStep)
    (result : SymbolicListSliceResult α)
    (evaluated : evaluateSymbolicListSlice heap sourceAllocation lower upper step = some result) :
    ∃ source bounded,
      heap.objects[sourceAllocation]? = some source ∧
      staticSliceIndices lower upper step source.length = some result.sourceIndices ∧
      result.heap.objects[result.allocation]? =
        some (selectSymbolicListIndices source result.sourceIndices bounded) := by
  unfold evaluateSymbolicListSlice at evaluated
  split at evaluated
  · contradiction
  · rename_i source sourceEq
    split at evaluated
    · contradiction
    · rename_i indices indicesEq
      dsimp at evaluated
      injection evaluated with resultEq
      subst result
      let bounded : ∀ index, index ∈ indices → index < source.length := fun index member =>
        every_static_slice_index_is_in_bounds lower upper step source.length index
          ⟨indices, indicesEq, member⟩
      refine ⟨source, bounded, sourceEq, indicesEq, ?_⟩
      simp

theorem successful_symbolic_slice_does_not_grow
    (heap : SymbolicListHeap α) (sourceAllocation : Nat)
    (lower upper : Option Int) (step : StaticSliceStep)
    (result : SymbolicListSliceResult α)
    (evaluated : evaluateSymbolicListSlice heap sourceAllocation lower upper step = some result) :
    ∃ source output,
      heap.objects[sourceAllocation]? = some source ∧
      result.heap.objects[result.allocation]? = some output ∧
      output.length ≤ source.length := by
  obtain ⟨source, bounded, sourceEq, indicesEq, resultEq⟩ :=
    successful_symbolic_slice_result_is_selected_source
      heap sourceAllocation lower upper step result evaluated
  refine ⟨source, selectSymbolicListIndices source result.sourceIndices bounded,
    sourceEq, resultEq, ?_⟩
  rw [selected_symbolic_list_length]
  exact static_slice_indices_do_not_grow lower upper step source.length result.sourceIndices
    indicesEq

theorem zero_step_symbolic_slice_refuses
    (heap : SymbolicListHeap α) (sourceAllocation : Nat)
    (lower upper : Option Int) :
    evaluateSymbolicListSlice heap sourceAllocation lower upper (.literal 0) = none := by
  unfold evaluateSymbolicListSlice
  cases heap.objects[sourceAllocation]? <;>
    simp [staticSliceIndices, normalizeStaticSlice]

theorem executable_symbolic_slice_allocates_reversed_result :
    evaluateSymbolicListSlice
        (α := Nat) ⟨[[10, 20, 30, 40]]⟩ 0 none none (.literal (-1)) =
      some {
        heap := ⟨[[10, 20, 30, 40], [40, 30, 20, 10]]⟩
        allocation := 1
        sourceIndices := [3, 2, 1, 0]
      } := by
  native_decide

theorem executable_symbolic_slice_preserves_selected_order_and_duplicates :
    evaluateSymbolicListSlice
        (α := Nat) ⟨[[7, 7, 8, 7]]⟩ 0 none none (.literal 2) =
      some {
        heap := ⟨[[7, 7, 8, 7], [7, 8]]⟩
        allocation := 1
        sourceIndices := [0, 2]
      } := by
  native_decide

end Maledictus
