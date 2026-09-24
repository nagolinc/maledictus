#![forbid(unsafe_code)]

use std::env;
use std::fs;
use std::process::ExitCode;

use maledictus::protocol::{ProofRequest, ProofStatus};

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(message) => {
            eprintln!("maledictus: {message}");
            ExitCode::from(64)
        }
    }
}

fn run() -> Result<ExitCode, String> {
    let arguments: Vec<String> = env::args().skip(1).collect();
    match arguments.as_slice() {
        [flag] if flag == "--version" => {
            println!("maledictus {}", maledictus::VERSION);
            Ok(ExitCode::SUCCESS)
        }
        [command] if command == "capabilities" => {
            let full_call_binding_refinement: serde_json::Value = serde_json::from_str(
                include_str!("../formal/extraction/call-binding-full/extraction.json"),
            )
            .map_err(|error| {
                format!("embedded full call-binding refinement metadata is invalid: {error}")
            })?;
            println!(
                "{}",
                serde_json::json!({
                    "schema": "maledictus-capabilities/v1",
                    "verifier": "maledictus",
                    "version": maledictus::VERSION,
                    "protocols": ["maledictus-verification-request/v4"],
                    "proof_obligations": ["no-undeclared-exceptional-exit"],
                    "implementation_refinements": [
                        {
                            "identity": full_call_binding_refinement["identity"],
                            "status": full_call_binding_refinement["status"],
                            "counts_as_implementation_refinement":
                                full_call_binding_refinement["counts_as_implementation_refinement"],
                            "scope": {
                                "rust_function": "call_binding::bind_call_with_allocator",
                                "production_wrapper": "call_binding::bind_call",
                                "specialization": "String/Int with total identity Clone and exact String equality semantics",
                                "universal_over": [
                                    "finite call signatures",
                                    "finite actual-item slices",
                                    "optional receivers",
                                    "every typed allocation outcome"
                                ],
                                "excludes": [
                                    "other type/value specializations",
                                    "the rest of Maledictus"
                                ]
                            },
                            "source": full_call_binding_refinement["source"],
                            "axiom_audits": full_call_binding_refinement["axiom_audits"],
                            "open_obligations": full_call_binding_refinement["open_obligations"]
                        }
                    ],
                    "languages": [
                        {
                            "language": "python",
                            "status": "ready",
                            "fragments": maledictus::fragments::PYTHON_CAPABILITIES
                        },
                        {
                            "language": "javascript",
                            "status": "ready",
                            "compiler": "typescript/5.9.3-checkJs",
                            "fragments": [maledictus::typescript::JAVASCRIPT_FRAGMENT]
                        },
                        {
                            "language": "typescript",
                            "status": "ready",
                            "compiler": "typescript/5.9.3",
                            "fragments": [maledictus::typescript::TYPESCRIPT_FRAGMENT]
                        }
                    ]
                })
            );
            Ok(ExitCode::SUCCESS)
        }
        [command, path] if command == "analyze-python" => {
            let source = fs::read_to_string(path)
                .map_err(|error| format!("cannot read Python source {path:?}: {error}"))?;
            let module = maledictus::python::analyze_module(&source, path)
                .map_err(|error| format!("cannot parse Python source {path:?}: {error}"))?;
            println!(
                "{}",
                serde_json::to_string(&module)
                    .map_err(|error| format!("cannot encode Python analysis: {error}"))?
            );
            Ok(ExitCode::SUCCESS)
        }
        [command, path] if command == "verify-contracts" => {
            let source = fs::read_to_string(path)
                .map_err(|error| format!("cannot read Python source {path:?}: {error}"))?;
            let verification = maledictus::python_contracts::verify_contract_module(
                &source,
                path,
                &[],
            )
            .map_err(|error| format!("{}: {}", error.code, error.message))?;
            let exit_code = if verification.passed {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            };
            println!(
                "{}",
                serde_json::to_string(&verification)
                    .map_err(|error| format!("cannot encode contract verification: {error}"))?
            );
            Ok(exit_code)
        }
        [command, path] if command == "verify-heap-contracts" => {
            let source = fs::read_to_string(path)
                .map_err(|error| format!("cannot read Python source {path:?}: {error}"))?;
            let verification = maledictus::python_heap_contracts::verify_heap_module(
                &source,
                path,
                &[],
            )
            .map_err(|error| format!("{}: {}", error.code, error.message))?;
            let exit_code = if verification.passed {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            };
            println!(
                "{}",
                serde_json::to_string(&verification)
                    .map_err(|error| format!("cannot encode heap verification: {error}"))?
            );
            Ok(exit_code)
        }
        [command, subcommand, suite_flag, suite, pin_flag, pin]
            if command == "conformance"
                && subcommand == "inventory"
                && suite_flag == "--suite"
                && pin_flag == "--pin" =>
        {
            let inventory = maledictus::conformance::inventory_pinned_nagini(
                std::path::Path::new(suite),
                std::path::Path::new(pin),
            )?;
            println!(
                "{}",
                serde_json::to_string(&inventory)
                    .map_err(|error| format!("cannot encode inventory: {error}"))?
            );
            Ok(ExitCode::SUCCESS)
        }
        [command, subcommand, suite_flag, suite, pin_flag, pin, fixture_flag, fixture]
            if command == "conformance"
                && subcommand == "check-scalar"
                && suite_flag == "--suite"
                && pin_flag == "--pin"
                && fixture_flag == "--fixture" =>
        {
            let result = maledictus::conformance::check_pinned_scalar_fixture(
                std::path::Path::new(suite),
                std::path::Path::new(pin),
                fixture,
            )?;
            let exit_code = if result.passed {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            };
            println!(
                "{}",
                serde_json::to_string(&result)
                    .map_err(|error| format!("cannot encode conformance result: {error}"))?
            );
            Ok(exit_code)
        }
        [command, subcommand, suite_flag, suite, pin_flag, pin, manifest_flag, manifest]
            if command == "conformance"
                && subcommand == "check-scalar-suite"
                && suite_flag == "--suite"
                && pin_flag == "--pin"
                && manifest_flag == "--manifest" =>
        {
            let result = maledictus::conformance::check_pinned_scalar_suite(
                std::path::Path::new(suite),
                std::path::Path::new(pin),
                std::path::Path::new(manifest),
            )?;
            let exit_code = if result.passed {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            };
            println!(
                "{}",
                serde_json::to_string(&result)
                    .map_err(|error| format!("cannot encode suite conformance result: {error}"))?
            );
            Ok(exit_code)
        }
        [command, subcommand, suite_flag, suite, pin_flag, pin, fixture_flag, fixture]
            if command == "conformance"
                && subcommand == "check-heap"
                && suite_flag == "--suite"
                && pin_flag == "--pin"
                && fixture_flag == "--fixture" =>
        {
            let result = maledictus::conformance::check_pinned_heap_fixture(
                std::path::Path::new(suite),
                std::path::Path::new(pin),
                fixture,
            )?;
            let exit_code = if result.passed {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            };
            println!(
                "{}",
                serde_json::to_string(&result)
                    .map_err(|error| format!("cannot encode heap conformance result: {error}"))?
            );
            Ok(exit_code)
        }
        [command, subcommand, suite_flag, suite, pin_flag, pin, manifest_flag, manifest]
            if command == "conformance"
                && subcommand == "check-heap-suite"
                && suite_flag == "--suite"
                && pin_flag == "--pin"
                && manifest_flag == "--manifest" =>
        {
            let result = maledictus::conformance::check_pinned_heap_suite(
                std::path::Path::new(suite),
                std::path::Path::new(pin),
                std::path::Path::new(manifest),
            )?;
            let exit_code = if result.passed {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            };
            println!(
                "{}",
                serde_json::to_string(&result).map_err(|error| format!(
                    "cannot encode heap suite conformance result: {error}"
                ))?
            );
            Ok(exit_code)
        }
        [command, subcommand, suite_flag, suite, pin_flag, pin, fixture_flag, fixture]
            if command == "conformance"
                && subcommand == "check-reference"
                && suite_flag == "--suite"
                && pin_flag == "--pin"
                && fixture_flag == "--fixture" =>
        {
            let result = maledictus::conformance::check_pinned_reference_fixture(
                std::path::Path::new(suite),
                std::path::Path::new(pin),
                fixture,
            )?;
            let exit_code = if result.passed {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            };
            println!(
                "{}",
                serde_json::to_string(&result).map_err(|error| format!(
                    "cannot encode reference conformance result: {error}"
                ))?
            );
            Ok(exit_code)
        }
        [command, subcommand, suite_flag, suite, pin_flag, pin, manifest_flag, manifest]
            if command == "conformance"
                && subcommand == "check-reference-suite"
                && suite_flag == "--suite"
                && pin_flag == "--pin"
                && manifest_flag == "--manifest" =>
        {
            let result = maledictus::conformance::check_pinned_reference_suite(
                std::path::Path::new(suite),
                std::path::Path::new(pin),
                std::path::Path::new(manifest),
            )?;
            let exit_code = if result.passed {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            };
            println!(
                "{}",
                serde_json::to_string(&result).map_err(|error| format!(
                    "cannot encode reference suite conformance result: {error}"
                ))?
            );
            Ok(exit_code)
        }
        [command, subcommand, suite_flag, suite, pin_flag, pin, root_flag, root]
            if command == "conformance"
                && subcommand == "classify-scalar"
                && suite_flag == "--suite"
                && pin_flag == "--pin"
                && root_flag == "--root" =>
        {
            let report = maledictus::conformance::classify_pinned_scalar_tree(
                std::path::Path::new(suite),
                std::path::Path::new(pin),
                root,
            )?;
            println!(
                "{}",
                serde_json::to_string(&report)
                    .map_err(|error| format!("cannot encode classification report: {error}"))?
            );
            Ok(ExitCode::SUCCESS)
        }
        [command, subcommand, suite_flag, suite, pin_flag, pin, root_flag, root]
            if command == "conformance"
                && subcommand == "classify-heap"
                && suite_flag == "--suite"
                && pin_flag == "--pin"
                && root_flag == "--root" =>
        {
            let report = maledictus::conformance::classify_pinned_heap_tree(
                std::path::Path::new(suite),
                std::path::Path::new(pin),
                root,
            )?;
            println!(
                "{}",
                serde_json::to_string(&report)
                    .map_err(|error| format!("cannot encode heap classification report: {error}"))?
            );
            Ok(ExitCode::SUCCESS)
        }
        [command, subcommand, suite_flag, suite, pin_flag, pin]
            if command == "conformance"
                && subcommand == "classify-suite"
                && suite_flag == "--suite"
                && pin_flag == "--pin" =>
        {
            let started = std::time::Instant::now();
            let mut progress = |event| match event {
                maledictus::conformance::ClassificationProgressEvent::FixtureStarted {
                    lane,
                    root,
                    fixture,
                    ordinal,
                    total,
                } => {
                    eprintln!(
                        "[classify-suite] {} {root} {ordinal}/{total}: {fixture}",
                        lane.label()
                    );
                }
                maledictus::conformance::ClassificationProgressEvent::LaneCompleted {
                    lane,
                    root,
                    total,
                } => {
                    eprintln!(
                        "[classify-suite] {} {root} complete: {total}/{total}",
                        lane.label()
                    );
                }
            };
            let report = maledictus::conformance::
                classify_pinned_combined_suite_parallel_with_progress_and_cache(
                    std::path::Path::new(suite),
                    std::path::Path::new(pin),
                    &maledictus::conformance::default_classifier_cache_root(),
                    &mut progress,
                )?;
            eprintln!(
                "[classify-suite] complete: {} fixtures in {:.1}s",
                report.total,
                started.elapsed().as_secs_f64()
            );
            println!(
                "{}",
                serde_json::to_string(&report)
                    .map_err(|error| format!("cannot encode combined classification report: {error}"))?
            );
            Ok(ExitCode::SUCCESS)
        }
        [command, flag, path] if command == "verify" && flag == "--request" => {
            let source = fs::read_to_string(path)
                .map_err(|error| format!("cannot read request {path:?}: {error}"))?;
            let request: ProofRequest = serde_json::from_str(&source)
                .map_err(|error| format!("invalid request {path:?}: {error}"))?;
            let response = maledictus::verify(&request);
            let exit_code = match response.status {
                ProofStatus::Proved => ExitCode::SUCCESS,
                ProofStatus::Refuted => ExitCode::from(1),
                ProofStatus::Refused => ExitCode::from(2),
            };
            println!(
                "{}",
                serde_json::to_string(&response)
                    .map_err(|error| format!("cannot encode response: {error}"))?
            );
            Ok(exit_code)
        }
        _ => Err(
            "usage: maledictus --version | capabilities | analyze-python FILE.py | verify-contracts FILE.py | conformance inventory --suite NAGINI --pin PIN.json | conformance check-scalar --suite NAGINI --pin PIN.json --fixture FILE.py | conformance check-scalar-suite --suite NAGINI --pin PIN.json --manifest FIXTURES.json | conformance check-heap --suite NAGINI --pin PIN.json --fixture FILE.py | conformance check-heap-suite --suite NAGINI --pin PIN.json --manifest FIXTURES.json | conformance check-reference --suite NAGINI --pin PIN.json --fixture FILE.py | conformance check-reference-suite --suite NAGINI --pin PIN.json --manifest FIXTURES.json | conformance classify-scalar --suite NAGINI --pin PIN.json --root FIXTURE_ROOT | conformance classify-heap --suite NAGINI --pin PIN.json --root FIXTURE_ROOT | conformance classify-suite --suite NAGINI --pin PIN.json | verify --request REQUEST.json".to_owned(),
        ),
    }
}
