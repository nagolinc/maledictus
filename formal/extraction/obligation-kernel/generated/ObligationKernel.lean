namespace ObligationKernel

inductive Measure where
  | known : Int -> Measure
  | unknown : String -> Measure
  | unbounded : Measure
  deriving DecidableEq, Repr

inductive ProduceDecision where
  | produce
  | collision
  deriving DecidableEq, Repr

inductive ConsumePolicy where
  | anySufficient
  | positiveCountdownTransfer
  | unboundedRequiresUnboundedOwner
  deriving DecidableEq, Repr

inductive ConsumeDecision where
  | consume
  | insufficient
  deriving DecidableEq, Repr

inductive CloseDecision where
  | closed
  | reportLeak
  | leakAlreadyReported
  deriving DecidableEq, Repr

def measureSatisfies (owned required : Measure) : Bool :=
  match owned, required with
  | .known owned, .known required => required <= owned
  | .unknown owned, .unknown required => owned == required
  | .unbounded, .unbounded => true
  | .unbounded, .known _ => true
  | _, _ => false

def decideProduce (slotOccupied : Bool) : ProduceDecision :=
  if slotOccupied then .collision else .produce

def decideConsume
    (owned : Option Measure)
    (required : Measure)
    (ownerIsBounded : Bool)
    (policy : ConsumePolicy) : ConsumeDecision :=
  match owned with
  | none => .insufficient
  | some owned =>
      let positiveTransfer :=
        policy == .positiveCountdownTransfer &&
          match owned, required with
          | .known owned, .known required => 0 < owned && 0 < required
          | _, _ => false
      if !(positiveTransfer || measureSatisfies owned required) then .insufficient
      else if policy == .unboundedRequiresUnboundedOwner &&
          required == .unbounded && ownerIsBounded then .insufficient
      else .consume

def decideClose (hasPending boundaryLeakReported : Bool) : CloseDecision :=
  match hasPending, boundaryLeakReported with
  | false, _ => .closed
  | true, false => .reportLeak
  | true, true => .leakAlreadyReported

def preservesLoopInvariant (owned : Option Measure) (invariant : Measure) : Bool :=
  match owned, invariant with
  | some .unbounded, .unbounded => true
  | some .unbounded, .known _ => true
  | some (.known owned), .known required => owned == required
  | some (.unknown owned), .unknown required => owned == required
  | _, _ => false

/-- A semantic interface for the five production functions. The checked Rust source hash binds
the concrete implementation; a future mechanical extraction can discharge `Corresponds`
without changing any transition theorem. -/
structure RustKernel where
  measureSatisfies : Measure -> Measure -> Bool
  decideProduce : Bool -> ProduceDecision
  decideConsume : Option Measure -> Measure -> Bool -> ConsumePolicy -> ConsumeDecision
  decideClose : Bool -> Bool -> CloseDecision
  preservesLoopInvariant : Option Measure -> Measure -> Bool

def modelKernel : RustKernel where
  measureSatisfies := measureSatisfies
  decideProduce := decideProduce
  decideConsume := decideConsume
  decideClose := decideClose
  preservesLoopInvariant := preservesLoopInvariant

structure Corresponds (implementation : RustKernel) : Prop where
  measureSatisfiesExact : implementation.measureSatisfies = measureSatisfies
  decideProduceExact : implementation.decideProduce = decideProduce
  decideConsumeExact : implementation.decideConsume = decideConsume
  decideCloseExact : implementation.decideClose = decideClose
  preservesLoopInvariantExact :
    implementation.preservesLoopInvariant = preservesLoopInvariant

end ObligationKernel
