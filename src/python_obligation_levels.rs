//! Source-independent wait-level and lock-order semantics for Python obligations.
//!
//! This module deliberately does not resolve Python spellings.  A frontend may enter this
//! kernel only after its resolver has certified both the verifier intrinsic and the runtime
//! object identity.  Relations are explicit evidence: the kernel never invents totality or a
//! transitive closure.

use std::collections::{BTreeMap, BTreeSet};

use crate::python_verifier_intrinsics::{
    CANONICAL_OBLIGATIONS_MODULE, VerifierIntrinsicFunctionDescriptor, VerifierIntrinsicKind,
    VerifierIntrinsicProvider, VerifierIntrinsicType,
};

/// Opaque capability proving that the exact canonical Level and WaitLevel descriptors were
/// obtained from the validated obligations provider.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedLevelIntrinsics {
    level: VerifierIntrinsicFunctionDescriptor,
    wait_level: VerifierIntrinsicFunctionDescriptor,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LevelIntrinsicCertificationFailure {
    WrongProviderModule,
    MissingLevel,
    MissingWaitLevel,
    InvalidLevelDescriptor,
    InvalidWaitLevelDescriptor,
}

/// A resolver-certified intrinsic occurrence. This is distinct from LevelIdentity, which
/// identifies a runtime object rather than verifier-owned syntax.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LevelIntrinsicEventKind {
    Level,
    WaitLevel,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedLevelIntrinsicEvent {
    descriptor: VerifierIntrinsicFunctionDescriptor,
    kind: LevelIntrinsicEventKind,
}

impl CertifiedLevelIntrinsicEvent {
    pub fn kind(&self) -> LevelIntrinsicEventKind {
        self.kind
    }
}

/// Resolver-produced local bindings for verifier-owned level intrinsics.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResolvedLevelIntrinsicBindings {
    by_local_name: BTreeMap<String, CertifiedLevelIntrinsicEvent>,
}

impl ResolvedLevelIntrinsicBindings {
    pub(crate) fn from_resolver_descriptors(
        certified: &CertifiedLevelIntrinsics,
        descriptors: &BTreeMap<String, VerifierIntrinsicFunctionDescriptor>,
    ) -> Self {
        let by_local_name = descriptors
            .iter()
            .filter_map(|(local_name, descriptor)| {
                certified
                    .classify_resolved_descriptor(descriptor)
                    .map(|event| (local_name.clone(), event))
            })
            .collect();
        Self { by_local_name }
    }

    pub fn event(&self, local_name: &str) -> Option<&CertifiedLevelIntrinsicEvent> {
        self.by_local_name.get(local_name)
    }

    pub fn is_empty(&self) -> bool {
        self.by_local_name.is_empty()
    }

    pub(crate) fn remove_local_binding(&mut self, local_name: &str) {
        self.by_local_name.remove(local_name);
    }
}

impl CertifiedLevelIntrinsics {
    pub(crate) fn from_validated_provider(
        provider: &VerifierIntrinsicProvider,
    ) -> Result<Self, LevelIntrinsicCertificationFailure> {
        if provider.module != CANONICAL_OBLIGATIONS_MODULE {
            return Err(LevelIntrinsicCertificationFailure::WrongProviderModule);
        }
        let level = descriptor_by_kind(provider, VerifierIntrinsicKind::Level)
            .ok_or(LevelIntrinsicCertificationFailure::MissingLevel)?;
        let wait_level = descriptor_by_kind(provider, VerifierIntrinsicKind::WaitLevel)
            .ok_or(LevelIntrinsicCertificationFailure::MissingWaitLevel)?;
        if !valid_level_descriptor(level) {
            return Err(LevelIntrinsicCertificationFailure::InvalidLevelDescriptor);
        }
        if !valid_wait_level_descriptor(wait_level) {
            return Err(LevelIntrinsicCertificationFailure::InvalidWaitLevelDescriptor);
        }
        Ok(Self {
            level: level.clone(),
            wait_level: wait_level.clone(),
        })
    }

    /// Classify a descriptor supplied by the canonical import resolver.
    ///
    /// Source spellings are irrelevant: aliases resolve to the same descriptor, while shadowed
    /// or rebound names have no descriptor and therefore cannot create an event.
    pub fn classify_resolved_descriptor(
        &self,
        descriptor: &VerifierIntrinsicFunctionDescriptor,
    ) -> Option<CertifiedLevelIntrinsicEvent> {
        if descriptor == &self.level {
            Some(CertifiedLevelIntrinsicEvent {
                descriptor: descriptor.clone(),
                kind: LevelIntrinsicEventKind::Level,
            })
        } else if descriptor == &self.wait_level {
            Some(CertifiedLevelIntrinsicEvent {
                descriptor: descriptor.clone(),
                kind: LevelIntrinsicEventKind::WaitLevel,
            })
        } else {
            None
        }
    }
}

fn descriptor_by_kind(
    provider: &VerifierIntrinsicProvider,
    kind: VerifierIntrinsicKind,
) -> Option<&VerifierIntrinsicFunctionDescriptor> {
    let mut matching = provider
        .functions
        .values()
        .filter(|descriptor| descriptor.kind == kind);
    let descriptor = matching.next()?;
    matching.next().is_none().then_some(descriptor)
}

fn valid_level_descriptor(descriptor: &VerifierIntrinsicFunctionDescriptor) -> bool {
    descriptor.kind == VerifierIntrinsicKind::Level
        && descriptor.canonical_identity == format!("{CANONICAL_OBLIGATIONS_MODULE}.Level")
        && descriptor.parameters.len() == 1
        && descriptor.result == VerifierIntrinsicType::Level
}

fn valid_wait_level_descriptor(descriptor: &VerifierIntrinsicFunctionDescriptor) -> bool {
    descriptor.kind == VerifierIntrinsicKind::WaitLevel
        && descriptor.canonical_identity == format!("{CANONICAL_OBLIGATIONS_MODULE}.WaitLevel")
        && descriptor.parameters.is_empty()
        && descriptor.result == VerifierIntrinsicType::Level
}

/// A resolver-certified runtime object identity whose lock level is stable.
///
/// The representation and constructor are private.  Frontends can obtain identities only
/// through [`LevelState::certify_resolved_object`], at the point where their canonical resolver
/// has already established stable object identity.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LevelIdentity {
    stable_key: String,
}

/// The lower endpoint of an explicitly asserted level-order relation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum LowerLevel {
    /// The unknown-but-stable wait level at the current function boundary.
    Ambient,
    /// The level of a currently-held runtime object.
    Object(LevelIdentity),
}

/// Stable evidence for one exact order relation.
///
/// Evidence is intentionally opaque.  In particular, possessing `a < b` and `b < c` does not
/// construct `a < c`; a frontend that proves such a relation must assert that third relation
/// explicitly.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LevelOrderEvidence {
    lower: LowerLevel,
    upper: LevelIdentity,
}

/// The source context in which `WaitLevel() < Level(object)` is being checked.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LevelRequirementContext {
    FunctionPrecondition,
    FunctionPostcondition,
    LoopInvariantEntry,
    LoopInvariantPreservation,
    CallPrecondition,
    LockAcquire,
    StableObjectOrder,
}

/// A precise reason why a wait-level requirement cannot be discharged.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LevelRequirementFailure {
    MissingOrderEvidence {
        context: LevelRequirementContext,
        target: LevelIdentity,
    },
}

/// Result of checking a context-sensitive wait-level requirement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LevelRequirementDecision {
    Satisfied,
    Failed(LevelRequirementFailure),
}

/// Path-local wait-level state.
///
/// Lock ownership is modeled by the separate linear MustRelease ledger. Acquiring a lock does
/// not rewrite a stable wait-level predicate.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LevelState {
    evidence: BTreeSet<LevelOrderEvidence>,
}

impl LevelState {
    /// Intern a stable object identity after the source resolver has certified it.
    ///
    /// This is crate-visible rather than public because arbitrary clients must not manufacture
    /// identities from source spelling.  The obligation frontend is responsible for calling it
    /// only with its canonical heap/resolver identity.
    pub(crate) fn certify_resolved_object(stable_key: impl Into<String>) -> LevelIdentity {
        LevelIdentity {
            stable_key: stable_key.into(),
        }
    }

    fn current_lower(&self) -> LowerLevel {
        LowerLevel::Ambient
    }

    /// Record one relation asserted by a checked precondition/invariant or proved by a provider.
    pub fn assert_current_below(&mut self, target: LevelIdentity) -> LevelOrderEvidence {
        let evidence = LevelOrderEvidence {
            lower: self.current_lower(),
            upper: target,
        };
        self.evidence.insert(evidence.clone());
        evidence
    }

    /// Record a provider-proved stable relation between two object levels.
    pub fn assert_object_below(
        &mut self,
        lower: LevelIdentity,
        upper: LevelIdentity,
    ) -> LevelOrderEvidence {
        let evidence = LevelOrderEvidence {
            lower: LowerLevel::Object(lower),
            upper,
        };
        self.evidence.insert(evidence.clone());
        evidence
    }

    /// Check exactly `WaitLevel() < Level(target)` in the supplied context.
    pub fn require_current_below(
        &self,
        target: &LevelIdentity,
        context: LevelRequirementContext,
    ) -> LevelRequirementDecision {
        let required = LevelOrderEvidence {
            lower: self.current_lower(),
            upper: target.clone(),
        };
        if self.evidence.contains(&required) {
            LevelRequirementDecision::Satisfied
        } else {
            LevelRequirementDecision::Failed(LevelRequirementFailure::MissingOrderEvidence {
                context,
                target: target.clone(),
            })
        }
    }

    /// Acquire a lock only when the exact current wait-level relation is available.
    pub fn acquire(&self, target: &LevelIdentity) -> LevelRequirementDecision {
        self.require_current_below(target, LevelRequirementContext::LockAcquire)
    }

    pub fn require_object_below(
        &self,
        lower: &LevelIdentity,
        upper: &LevelIdentity,
    ) -> LevelRequirementDecision {
        let required = LevelOrderEvidence {
            lower: LowerLevel::Object(lower.clone()),
            upper: upper.clone(),
        };
        if self.evidence.contains(&required) {
            LevelRequirementDecision::Satisfied
        } else {
            LevelRequirementDecision::Failed(LevelRequirementFailure::MissingOrderEvidence {
                context: LevelRequirementContext::StableObjectOrder,
                target: upper.clone(),
            })
        }
    }

    /// Restore order evidence from a previously checked path state.
    pub fn import_evidence(&mut self, evidence: &LevelOrderEvidence) {
        self.evidence.insert(evidence.clone());
    }

    pub fn has_order_evidence(&self) -> bool {
        !self.evidence.is_empty()
    }

    pub(crate) fn forget_identity(&mut self, target: &LevelIdentity) {
        self.evidence.retain(|evidence| {
            evidence.upper != *target
                && !matches!(&evidence.lower, LowerLevel::Object(lower) if lower == target)
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::python_verifier_intrinsics::validate_canonical_obligations_provider;

    const PROVIDER: &str = include_str!("../.upstream/nagini/src/nagini_contracts/obligations.py");

    fn identity(name: &str) -> LevelIdentity {
        LevelState::certify_resolved_object(name)
    }

    #[test]
    fn only_exact_validated_descriptors_create_intrinsic_events() {
        let provider = validate_canonical_obligations_provider(PROVIDER, "obligations.py")
            .expect("canonical provider");
        let intrinsics = CertifiedLevelIntrinsics::from_validated_provider(&provider)
            .expect("level descriptors");
        let level = provider
            .functions
            .values()
            .find(|descriptor| descriptor.kind == VerifierIntrinsicKind::Level)
            .expect("Level descriptor");
        let wait_level = provider
            .functions
            .values()
            .find(|descriptor| descriptor.kind == VerifierIntrinsicKind::WaitLevel)
            .expect("WaitLevel descriptor");
        let must_release = provider
            .functions
            .values()
            .find(|descriptor| descriptor.kind == VerifierIntrinsicKind::MustRelease)
            .expect("MustRelease descriptor");

        assert_eq!(
            intrinsics
                .classify_resolved_descriptor(level)
                .map(|event| event.kind()),
            Some(LevelIntrinsicEventKind::Level)
        );
        assert_eq!(
            intrinsics
                .classify_resolved_descriptor(wait_level)
                .map(|event| event.kind()),
            Some(LevelIntrinsicEventKind::WaitLevel)
        );
        assert_eq!(intrinsics.classify_resolved_descriptor(must_release), None);
    }

    #[test]
    fn descriptor_kind_or_identity_drift_cannot_be_recertified() {
        let mut provider = validate_canonical_obligations_provider(PROVIDER, "obligations.py")
            .expect("canonical provider");
        let level = provider
            .functions
            .values_mut()
            .find(|descriptor| descriptor.kind == VerifierIntrinsicKind::Level)
            .expect("Level descriptor");
        level.canonical_identity = "application.Level".to_owned();
        assert_eq!(
            CertifiedLevelIntrinsics::from_validated_provider(&provider),
            Err(LevelIntrinsicCertificationFailure::InvalidLevelDescriptor)
        );
    }

    #[test]
    fn acquire_requires_exact_current_order_evidence() {
        let first = identity("first");
        let second = identity("second");
        let mut state = LevelState::default();

        state.assert_current_below(first.clone());
        assert_eq!(state.acquire(&first), LevelRequirementDecision::Satisfied);
        assert_eq!(
            state.acquire(&second),
            LevelRequirementDecision::Failed(LevelRequirementFailure::MissingOrderEvidence {
                context: LevelRequirementContext::LockAcquire,
                target: second.clone(),
            })
        );

        state.assert_current_below(second.clone());
        assert_eq!(state.acquire(&second), LevelRequirementDecision::Satisfied);
    }

    #[test]
    fn object_order_is_independent_from_wait_level_order() {
        let first = identity("first");
        let second = identity("second");
        let mut state = LevelState::default();
        state.assert_object_below(first.clone(), second.clone());
        assert_eq!(
            state.require_object_below(&first, &second),
            LevelRequirementDecision::Satisfied
        );
        assert_ne!(state.acquire(&second), LevelRequirementDecision::Satisfied);
    }

    #[test]
    fn evidence_does_not_gain_an_implicit_transitive_closure() {
        let first = identity("first");
        let second = identity("second");
        let third = identity("third");
        let mut state = LevelState::default();
        state.assert_current_below(first.clone());
        state.assert_object_below(first.clone(), second.clone());
        state.assert_object_below(second, third.clone());

        assert_eq!(
            state.require_object_below(&first, &third),
            LevelRequirementDecision::Failed(LevelRequirementFailure::MissingOrderEvidence {
                context: LevelRequirementContext::StableObjectOrder,
                target: third,
            })
        );
    }
}
