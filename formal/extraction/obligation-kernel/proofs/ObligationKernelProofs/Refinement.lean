import ObligationKernel

namespace ObligationKernel.Proofs

def TransitionLaws (kernel : RustKernel) : Prop :=
  kernel.decideProduce false = .produce /\
  kernel.decideProduce true = .collision /\
  (forall required bounded policy,
    kernel.decideConsume none required bounded policy = .insufficient) /\
  (forall owned required bounded policy,
    kernel.decideConsume (some owned) required bounded policy =
      decideConsume (some owned) required bounded policy) /\
  kernel.decideClose false false = .closed /\
  kernel.decideClose false true = .closed /\
  kernel.decideClose true false = .reportLeak /\
  kernel.decideClose true true = .leakAlreadyReported /\
  kernel.preservesLoopInvariant (some (.known 1)) (.known 1) = true /\
  kernel.preservesLoopInvariant (some (.known 2)) (.known 1) = false /\
  kernel.preservesLoopInvariant (some .unbounded) (.known 1) = true

theorem model_transition_laws : TransitionLaws modelKernel := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro required bounded policy
    rfl
  constructor
  · intro owned required bounded policy
    rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

/-- Conditional source-correspondence theorem. It proves all production transition laws from one
explicit premise stating that the source-bound Rust functions equal the checked model. The
coverage manifest classifies this as conditional until mechanical Rust extraction closes that
premise. -/
theorem source_transition_semantics
    (implementation : RustKernel)
    (correspondence : Corresponds implementation) :
    TransitionLaws implementation := by
  rcases correspondence with
    ⟨_, produceExact, consumeExact, closeExact, preserveExact⟩
  unfold TransitionLaws at ⊢
  rw [produceExact, consumeExact, closeExact, preserveExact]
  exact model_transition_laws

theorem decide_produce_deterministic
    (kernel : RustKernel)
    (occupied : Bool) (left right : ProduceDecision)
    (leftResult : kernel.decideProduce occupied = left)
    (rightResult : kernel.decideProduce occupied = right) : left = right := by
  rw [← leftResult, ← rightResult]

theorem decide_consume_deterministic
    (kernel : RustKernel)
    (owned : Option Measure) (required : Measure) (bounded : Bool)
    (policy : ConsumePolicy) (left right : ConsumeDecision)
    (leftResult : kernel.decideConsume owned required bounded policy = left)
    (rightResult : kernel.decideConsume owned required bounded policy = right) : left = right := by
  rw [← leftResult, ← rightResult]

theorem decide_close_deterministic
    (kernel : RustKernel)
    (pending reported : Bool) (left right : CloseDecision)
    (leftResult : kernel.decideClose pending reported = left)
    (rightResult : kernel.decideClose pending reported = right) : left = right := by
  rw [← leftResult, ← rightResult]

end ObligationKernel.Proofs
