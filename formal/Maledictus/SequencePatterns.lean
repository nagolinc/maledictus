namespace Maledictus

/-!
Model-only algebra for the bounded Python sequence-pattern fragment.

This is constructive documentation, not extracted Rust/frontend code and not a Rust-to-Lean
refinement proof. Production additionally checks real Python list and element types and lowers
element reads into the shared heap VC terms. A starred tail is deliberately absent from this
algebra: the frontend gives it the correct list sort but no content, length, or alias facts.
-/

inductive SequencePatternShape where
  | fixed (elements : Nat)
  | starred (headCount tailCount : Nat)
  deriving DecidableEq, Repr

def sequencePatternAccepts (shape : SequencePatternShape) (length : Nat) : Bool :=
  match shape with
  | .fixed elements => length == elements
  | .starred headCount tailCount => headCount + tailCount <= length

theorem fixed_pattern_accepts_exact_length (elements : Nat) :
    sequencePatternAccepts (.fixed elements) elements = true := by
  simp [sequencePatternAccepts]

theorem fixed_pattern_rejects_different_length (elements length : Nat)
    (different : length ≠ elements) :
    sequencePatternAccepts (.fixed elements) length = false := by
  simp [sequencePatternAccepts, different]

theorem starred_pattern_accepts_at_minimum (headCount tailCount : Nat) :
    sequencePatternAccepts (.starred headCount tailCount) (headCount + tailCount) = true := by
  simp [sequencePatternAccepts]

theorem starred_prefix_index_is_in_bounds
    (headCount tailCount length index : Nat)
    (accepted : sequencePatternAccepts (.starred headCount tailCount) length = true)
    (inPrefix : index < headCount) :
    index < length := by
  simp [sequencePatternAccepts] at accepted
  omega

theorem starred_suffix_index_is_in_bounds
    (headCount tailCount length distance : Nat)
    (accepted : sequencePatternAccepts (.starred headCount tailCount) length = true)
    (inSuffix : distance < tailCount) :
    distance < length := by
  simp [sequencePatternAccepts] at accepted
  omega

end Maledictus
