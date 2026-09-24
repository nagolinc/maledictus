//! AST-independent transition decisions for the linear obligation ledger.
//!
//! The Python frontend resolves source identities and contract clauses.  This module owns the
//! small state machine that decides whether a resolved obligation slot may be produced, consumed,
//! or reported at a function boundary.  Keeping these decisions free of Python ASTs makes the
//! production semantics directly testable and gives the formal model one exact, finite seam.

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Measure {
    Known(i64),
    Unknown(String),
    Unbounded,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProduceDecision {
    Produce,
    Collision,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ConsumePolicy {
    AnySufficient,
    PositiveCountdownTransfer,
    UnboundedRequiresUnboundedOwner,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ConsumeDecision {
    Consume,
    Insufficient,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CloseDecision {
    Closed,
    ReportLeak,
    LeakAlreadyReported,
}

pub(crate) fn measure_satisfies(owned: &Measure, required: &Measure) -> bool {
    match (owned, required) {
        (Measure::Known(owned), Measure::Known(required)) => owned >= required,
        (Measure::Unknown(owned), Measure::Unknown(required)) => owned == required,
        (Measure::Unbounded, Measure::Unbounded | Measure::Known(_)) => true,
        _ => false,
    }
}

pub(crate) fn decide_produce(slot_occupied: bool) -> ProduceDecision {
    if slot_occupied {
        ProduceDecision::Collision
    } else {
        ProduceDecision::Produce
    }
}

pub(crate) fn decide_consume(
    owned: Option<&Measure>,
    required: &Measure,
    owner_is_bounded: bool,
    policy: ConsumePolicy,
) -> ConsumeDecision {
    let Some(owned) = owned else {
        return ConsumeDecision::Insufficient;
    };
    let positive_countdown_transfer = policy == ConsumePolicy::PositiveCountdownTransfer
        && matches!((owned, required),
            (Measure::Known(owned), Measure::Known(required)) if *owned > 0 && *required > 0);
    if !positive_countdown_transfer && !measure_satisfies(owned, required) {
        return ConsumeDecision::Insufficient;
    }
    if policy == ConsumePolicy::UnboundedRequiresUnboundedOwner
        && *required == Measure::Unbounded
        && owner_is_bounded
    {
        return ConsumeDecision::Insufficient;
    }
    ConsumeDecision::Consume
}

pub(crate) fn decide_close(has_pending: bool, boundary_leak_reported: bool) -> CloseDecision {
    match (has_pending, boundary_leak_reported) {
        (false, _) => CloseDecision::Closed,
        (true, false) => CloseDecision::ReportLeak,
        (true, true) => CloseDecision::LeakAlreadyReported,
    }
}

pub(crate) fn preserves_loop_invariant(owned: Option<&Measure>, invariant: &Measure) -> bool {
    match (owned, invariant) {
        (Some(Measure::Unbounded), Measure::Unbounded | Measure::Known(_)) => true,
        (Some(Measure::Known(owned)), Measure::Known(required)) => owned == required,
        (Some(Measure::Unknown(owned)), Measure::Unknown(required)) => owned == required,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn measure_order_is_exact_for_every_measure_shape() {
        assert!(measure_satisfies(&Measure::Known(3), &Measure::Known(2)));
        assert!(!measure_satisfies(&Measure::Known(2), &Measure::Known(3)));
        assert!(measure_satisfies(
            &Measure::Unknown("n".to_owned()),
            &Measure::Unknown("n".to_owned())
        ));
        assert!(!measure_satisfies(
            &Measure::Unknown("n".to_owned()),
            &Measure::Unknown("m".to_owned())
        ));
        assert!(measure_satisfies(&Measure::Unbounded, &Measure::Known(8)));
        assert!(measure_satisfies(&Measure::Unbounded, &Measure::Unbounded));
        assert!(!measure_satisfies(&Measure::Known(8), &Measure::Unbounded));
    }

    #[test]
    fn production_is_linear_and_collision_preserves_the_existing_owner() {
        assert_eq!(decide_produce(false), ProduceDecision::Produce);
        assert_eq!(decide_produce(true), ProduceDecision::Collision);
    }

    #[test]
    fn consumption_requires_presence_measure_and_unbounded_policy() {
        let owned = Measure::Known(3);
        assert_eq!(
            decide_consume(
                Some(&owned),
                &Measure::Known(2),
                false,
                ConsumePolicy::AnySufficient
            ),
            ConsumeDecision::Consume
        );
        assert_eq!(
            decide_consume(
                None,
                &Measure::Known(1),
                false,
                ConsumePolicy::AnySufficient
            ),
            ConsumeDecision::Insufficient
        );
        assert_eq!(
            decide_consume(
                Some(&Measure::Known(1)),
                &Measure::Known(2),
                true,
                ConsumePolicy::PositiveCountdownTransfer
            ),
            ConsumeDecision::Consume
        );
        assert_eq!(
            decide_consume(
                Some(&Measure::Unbounded),
                &Measure::Unbounded,
                true,
                ConsumePolicy::UnboundedRequiresUnboundedOwner
            ),
            ConsumeDecision::Insufficient
        );
    }

    #[test]
    fn closure_reports_each_boundary_leak_at_most_once() {
        assert_eq!(decide_close(false, false), CloseDecision::Closed);
        assert_eq!(decide_close(false, true), CloseDecision::Closed);
        assert_eq!(decide_close(true, false), CloseDecision::ReportLeak);
        assert_eq!(decide_close(true, true), CloseDecision::LeakAlreadyReported);
    }

    #[test]
    fn bounded_loop_obligations_must_return_with_the_declared_measure() {
        assert!(preserves_loop_invariant(
            Some(&Measure::Known(1)),
            &Measure::Known(1)
        ));
        assert!(!preserves_loop_invariant(
            Some(&Measure::Known(2)),
            &Measure::Known(1)
        ));
        assert!(preserves_loop_invariant(
            Some(&Measure::Unbounded),
            &Measure::Known(1)
        ));
    }
}
