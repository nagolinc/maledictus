use serde::{Deserialize, Serialize};

/// Language-independent exceptional exits inferred from real source by a frontend.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ExitEffect {
    Return {
        type_name: String,
    },
    Raise {
        exception_type: String,
    },
    /// A frontend must use Unknown instead of silently dropping syntax or an unresolved call.
    Unknown {
        reason: String,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum KernelFailure {
    UnexpectedException(String),
    UnknownEffect(String),
    NoEffects,
}

/// Accept only when every inferred exit is known and every exceptional exit is explicitly allowed.
pub fn check_exit_effects(
    effects: &[ExitEffect],
    allowed_exceptions: &[String],
) -> Result<(), KernelFailure> {
    if effects.is_empty() {
        return Err(KernelFailure::NoEffects);
    }
    for effect in effects {
        match effect {
            ExitEffect::Return { .. } => {}
            ExitEffect::Raise { exception_type }
                if allowed_exceptions
                    .iter()
                    .any(|allowed| allowed == exception_type) => {}
            ExitEffect::Raise { exception_type } => {
                return Err(KernelFailure::UnexpectedException(exception_type.clone()));
            }
            ExitEffect::Unknown { reason } => {
                return Err(KernelFailure::UnknownEffect(reason.clone()));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_total_return_is_accepted() {
        assert_eq!(
            check_exit_effects(
                &[ExitEffect::Return {
                    type_name: "PreparedPrompt".to_owned(),
                }],
                &[],
            ),
            Ok(())
        );
    }

    #[test]
    fn an_explicitly_allowed_exception_is_accepted() {
        assert_eq!(
            check_exit_effects(
                &[ExitEffect::Raise {
                    exception_type: "PromptRejected".to_owned(),
                }],
                &["PromptRejected".to_owned()],
            ),
            Ok(())
        );
    }

    #[test]
    fn an_unexpected_exception_is_rejected() {
        assert_eq!(
            check_exit_effects(
                &[ExitEffect::Raise {
                    exception_type: "ValueError".to_owned(),
                }],
                &[],
            ),
            Err(KernelFailure::UnexpectedException("ValueError".to_owned()))
        );
    }

    #[test]
    fn an_unknown_effect_is_rejected() {
        assert_eq!(
            check_exit_effects(
                &[ExitEffect::Unknown {
                    reason: "unresolved callable field".to_owned(),
                }],
                &[],
            ),
            Err(KernelFailure::UnknownEffect(
                "unresolved callable field".to_owned()
            ))
        );
    }

    #[test]
    fn an_empty_frontend_result_is_not_a_vacuous_proof() {
        assert_eq!(check_exit_effects(&[], &[]), Err(KernelFailure::NoEffects));
    }
}
