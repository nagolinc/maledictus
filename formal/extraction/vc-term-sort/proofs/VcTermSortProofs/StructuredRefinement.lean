import VcTermSortProofs.RecursiveTermination
import VcTermSortProofs.RawRecursiveTermination
import VcTermSortProofs.NormalizationCorrespondence

open Aeneas Aeneas.Std Result ControlFlow Error

namespace VcTermSort.Proofs

/-- Exact implementation refinement for the source-bound typed `Term::sort`
entrypoint. Equality of `SortError` values preserves the constructor and every
structured diagnostic field; presentation-layer string rendering is not part
of this kernel claim. -/
structure StructuredTermSortRefinement : Prop where
  implementation : ∀ term,
    VcTermSort.term_sort_extraction_entrypoint term =
      VcTermSort.Term.sort_typed term
  success : ∀ term sort,
    VcTermSort.term_sort_extraction_entrypoint term =
        .ok (.Ok sort) ↔
      VcTermSort.Term.sort_typed term = .ok (.Ok sort)
  diagnostic : ∀ term error,
    VcTermSort.term_sort_extraction_entrypoint term =
        .ok (.Err error) ↔
      VcTermSort.Term.sort_typed term = .ok (.Err error)
  externalFailure : ∀ term failure,
    VcTermSort.term_sort_extraction_entrypoint term = .fail failure ↔
      VcTermSort.Term.sort_typed term = .fail failure
  noDivergence : ∀ term,
    VcTermSort.term_sort_extraction_entrypoint term ≠ .div

/-- Public all-input implementation-refinement theorem for the exact generated
typed entrypoint. The extraction wrapper neither changes successful sorts nor
collapses, invents, or rewrites any structured error outcome. -/
theorem term_sort_extraction_entrypoint_structured_refinement :
    StructuredTermSortRefinement := {
  implementation := entrypoint_is_term_sort
  success := by
    intro term sort
    rw [entrypoint_is_term_sort]
  diagnostic := by
    intro term error
    rw [entrypoint_is_term_sort]
  externalFailure := by
    intro term failure
    rw [entrypoint_is_term_sort]
  noDivergence := term_sort_extraction_entrypoint_terminates
}

/-- Exact all-input refinement from the generated `RawFuns` entrypoint through
the audited eleven-loop normalization to the terminating normalized model.
`RawFuns` is the extraction after the separately tracked compatibility
rewrites (including the constructive vector model); this theorem specifically
closes the semantic obligation introduced by replacing the eleven partial
fixpoint loops with their source-measure fuel implementations. -/
structure SourceBoundStructuredTermSortRefinement : Prop where
  implementation : ∀ term,
    VcTermSortRaw.term_sort_extraction_entrypoint term =
      VcTermSort.Term.sort_typed term
  success : ∀ term sort,
    VcTermSortRaw.term_sort_extraction_entrypoint term = .ok (.Ok sort) ↔
      VcTermSort.Term.sort_typed term = .ok (.Ok sort)
  diagnostic : ∀ term error,
    VcTermSortRaw.term_sort_extraction_entrypoint term = .ok (.Err error) ↔
      VcTermSort.Term.sort_typed term = .ok (.Err error)
  externalFailure : ∀ term failure,
    VcTermSortRaw.term_sort_extraction_entrypoint term = .fail failure ↔
      VcTermSort.Term.sort_typed term = .fail failure
  noDivergence : ∀ term,
    VcTermSortRaw.term_sort_extraction_entrypoint term ≠ .div

/-- Public structured outcome theorem for every input to the generated raw
typed entrypoint. Success values and every `SortError` constructor field are
preserved exactly; no result is inferred from a benchmark or a bounded sample.
-/
theorem raw_term_sort_extraction_entrypoint_structured_refinement :
    SourceBoundStructuredTermSortRefinement := {
  implementation := by
    intro term
    rw [raw_term_sort_extraction_entrypoint_eq_normalized]
    exact entrypoint_is_term_sort term
  success := by
    intro term sort
    rw [raw_term_sort_extraction_entrypoint_eq_normalized, entrypoint_is_term_sort]
  diagnostic := by
    intro term error
    rw [raw_term_sort_extraction_entrypoint_eq_normalized, entrypoint_is_term_sort]
  externalFailure := by
    intro term failure
    rw [raw_term_sort_extraction_entrypoint_eq_normalized, entrypoint_is_term_sort]
  noDivergence := by
    intro term
    rw [raw_term_sort_extraction_entrypoint_eq_normalized]
    exact term_sort_extraction_entrypoint_terminates term
}

end VcTermSort.Proofs
