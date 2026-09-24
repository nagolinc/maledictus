//! Typed, source-lexed evaluation of Nagini conformance annotations.

use rustpython_parser::{Mode, Tok, lexer::lex};
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum PythonImplementation {
    Cpython,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PythonLanguageProfile {
    pub implementation: PythonImplementation,
    pub major: u16,
    pub minor: u16,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum AnnotationPhase {
    Translation,
    Verification,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum AnnotationBackend {
    Any,
    Silicon,
    Carbon,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AnnotationProfile {
    pub root: String,
    pub phase: AnnotationPhase,
    pub backend: AnnotationBackend,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NaginiConformanceEnvironment {
    pub python: PythonLanguageProfile,
    pub nagini_tag: String,
    pub nagini_commit: String,
    pub annotation_profiles: Vec<AnnotationProfile>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SelectedAnnotationProfile {
    pub root: String,
    pub python: PythonLanguageProfile,
    pub nagini_tag: String,
    pub nagini_commit: String,
    pub phase: AnnotationPhase,
    pub backend: AnnotationBackend,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct IgnoreFileCondition {
    pub raw: String,
    pub line: u32,
    pub backend: AnnotationBackend,
    pub issue_id: String,
    pub active: bool,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct AnnotationProfileEvaluation {
    pub selected: SelectedAnnotationProfile,
    pub ignore_file_conditions: Vec<IgnoreFileCondition>,
    pub ignored: bool,
}

pub fn has_ignore_file_annotation(source: &str) -> Result<bool, String> {
    for token in lex(source, Mode::Module) {
        let (token, _) = token.map_err(|error| {
            format!("cannot lex Python source while locating conformance annotations: {error:?}")
        })?;
        let Tok::Comment(comment) = token else {
            continue;
        };
        let trimmed = comment.trim();
        let Some(contents) = trimmed.strip_prefix("#:: ") else {
            continue;
        };
        if contents
            .split("||")
            .map(str::trim)
            .any(|annotation| annotation.starts_with("IgnoreFile"))
        {
            return Ok(true);
        }
    }
    Ok(false)
}

pub fn evaluate_ignore_file_annotations(
    source: &str,
    selected: SelectedAnnotationProfile,
) -> Result<AnnotationProfileEvaluation, String> {
    let mut conditions = Vec::new();
    for token in lex(source, Mode::Module) {
        let (token, range) = token.map_err(|error| {
            format!("cannot lex Python source while evaluating conformance annotations: {error:?}")
        })?;
        let Tok::Comment(comment) = token else {
            continue;
        };
        let trimmed = comment.trim();
        let Some(contents) = trimmed.strip_prefix("#:: ") else {
            continue;
        };
        if !contents.ends_with(')') {
            if contents
                .split("||")
                .map(str::trim)
                .any(|part| part.starts_with("IgnoreFile"))
            {
                return Err(format!(
                    "malformed IgnoreFile annotation on line {}",
                    source_line(source, u32::from(range.start()))
                ));
            }
            continue;
        }
        for annotation in contents.split("||").map(str::trim) {
            if !annotation.starts_with("IgnoreFile") {
                continue;
            }
            let (backend, issue_id) = parse_ignore_file(annotation).map_err(|message| {
                format!(
                    "malformed IgnoreFile annotation on line {}: {message}",
                    source_line(source, u32::from(range.start()))
                )
            })?;
            let active = backend == AnnotationBackend::Any || backend == selected.backend;
            conditions.push(IgnoreFileCondition {
                raw: annotation.to_owned(),
                line: source_line(source, u32::from(range.start())),
                backend,
                issue_id,
                active,
            });
        }
    }
    let ignored = conditions.iter().any(|condition| condition.active);
    Ok(AnnotationProfileEvaluation {
        selected,
        ignore_file_conditions: conditions,
        ignored,
    })
}

fn parse_ignore_file(annotation: &str) -> Result<(AnnotationBackend, String), String> {
    let Some(mut rest) = annotation.strip_prefix("IgnoreFile") else {
        return Err("annotation does not begin with IgnoreFile".to_owned());
    };
    let first = take_group(&mut rest)?;
    let (backend, issue_id) = if rest.is_empty() {
        (AnnotationBackend::Any, first)
    } else {
        let backend = match first.as_str() {
            "silicon" => AnnotationBackend::Silicon,
            "carbon" => AnnotationBackend::Carbon,
            _ => {
                return Err(format!(
                    "unsupported backend condition {first:?}; expected silicon or carbon"
                ));
            }
        };
        (backend, take_group(&mut rest)?)
    };
    if !rest.is_empty() {
        return Err(format!("unexpected trailing text {rest:?}"));
    }
    if issue_id.is_empty() || !issue_id.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err("issue id must contain only decimal digits".to_owned());
    }
    Ok((backend, issue_id))
}

fn take_group(rest: &mut &str) -> Result<String, String> {
    let Some(contents) = rest.strip_prefix('(') else {
        return Err("expected an opening parenthesis".to_owned());
    };
    let Some(end) = contents.find(')') else {
        return Err("missing a closing parenthesis".to_owned());
    };
    let value = contents[..end].trim().to_owned();
    *rest = &contents[end + 1..];
    Ok(value)
}

fn source_line(source: &str, byte_offset: u32) -> u32 {
    let offset = usize::try_from(byte_offset)
        .unwrap_or(source.len())
        .min(source.len());
    u32::try_from(
        source[..offset]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1,
    )
    .unwrap_or(u32::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn selected(phase: AnnotationPhase, backend: AnnotationBackend) -> SelectedAnnotationProfile {
        SelectedAnnotationProfile {
            root: "tests/functional/verification".to_owned(),
            python: PythonLanguageProfile {
                implementation: PythonImplementation::Cpython,
                major: 3,
                minor: 12,
            },
            nagini_tag: "v1.3.1".to_owned(),
            nagini_commit: "91a13e4".to_owned(),
            phase,
            backend,
        }
    }

    #[test]
    fn unconditional_and_selected_backend_conditions_are_active() {
        let unconditional = evaluate_ignore_file_annotations(
            "#:: IgnoreFile(228)\nx = 1\n",
            selected(AnnotationPhase::Translation, AnnotationBackend::Any),
        )
        .unwrap();
        assert!(unconditional.ignored);
        assert_eq!(unconditional.ignore_file_conditions[0].issue_id, "228");
        assert_eq!(unconditional.ignore_file_conditions[0].line, 1);

        let silicon = evaluate_ignore_file_annotations(
            "#:: IgnoreFile(silicon)(101)\nx = 1\n",
            selected(AnnotationPhase::Verification, AnnotationBackend::Silicon),
        )
        .unwrap();
        assert!(silicon.ignored);
        assert_eq!(
            silicon.ignore_file_conditions[0].backend,
            AnnotationBackend::Silicon
        );
    }

    #[test]
    fn nonselected_backend_condition_is_audited_but_inactive() {
        let result = evaluate_ignore_file_annotations(
            "#:: IgnoreFile(carbon)(107)\nx = 1\n",
            selected(AnnotationPhase::Verification, AnnotationBackend::Silicon),
        )
        .unwrap();
        assert!(!result.ignored);
        assert_eq!(result.ignore_file_conditions.len(), 1);
        assert!(!result.ignore_file_conditions[0].active);
        assert_eq!(
            result.ignore_file_conditions[0].raw,
            "IgnoreFile(carbon)(107)"
        );
    }

    #[test]
    fn backend_condition_is_inactive_for_translation_any_profile() {
        let result = evaluate_ignore_file_annotations(
            "#:: IgnoreFile(silicon)(9)\nx = 1\n",
            selected(AnnotationPhase::Translation, AnnotationBackend::Any),
        )
        .unwrap();
        assert!(!result.ignored);
        assert!(!result.ignore_file_conditions[0].active);
    }

    #[test]
    fn lexer_ignores_annotation_text_inside_python_strings() {
        let result = evaluate_ignore_file_annotations(
            "value = '#:: IgnoreFile(3)'\n",
            selected(AnnotationPhase::Verification, AnnotationBackend::Silicon),
        )
        .unwrap();
        assert!(!result.ignored);
        assert!(result.ignore_file_conditions.is_empty());
        assert!(!has_ignore_file_annotation("value = '#:: IgnoreFile(3)'\n").unwrap());
        assert!(has_ignore_file_annotation("#:: IgnoreFile(3)\n").unwrap());
    }

    #[test]
    fn multiple_annotations_are_parsed_structurally() {
        let result = evaluate_ignore_file_annotations(
            "#:: ExpectedOutput(assert.failed) || IgnoreFile(carbon)(8) || IgnoreFile(9)\n",
            selected(AnnotationPhase::Verification, AnnotationBackend::Silicon),
        )
        .unwrap();
        assert!(result.ignored);
        assert_eq!(result.ignore_file_conditions.len(), 2);
        assert!(!result.ignore_file_conditions[0].active);
        assert!(result.ignore_file_conditions[1].active);
    }

    #[test]
    fn malformed_or_unsupported_conditions_fail_closed() {
        for source in [
            "#:: IgnoreFile(foo)(1)\n",
            "#:: IgnoreFile(silicon)(not-an-issue)\n",
            "#:: IgnoreFile(1)trailing\n",
            "#:: IgnoreFile(1\n",
        ] {
            assert!(
                evaluate_ignore_file_annotations(
                    source,
                    selected(AnnotationPhase::Verification, AnnotationBackend::Silicon),
                )
                .is_err(),
                "malformed annotation unexpectedly accepted: {source:?}"
            );
        }
    }
}
