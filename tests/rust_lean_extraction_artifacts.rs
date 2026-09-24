use std::fs;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

fn project_path(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(relative)
}

fn sha256(path: &Path) -> String {
    let bytes = fs::read(path).unwrap_or_else(|error| {
        panic!(
            "failed to read extraction artifact {}: {error}",
            path.display()
        )
    });
    format!("{:x}", Sha256::digest(bytes))
}

fn assert_recorded_hash(record: &serde_json::Value) {
    let relative = record["path"].as_str().expect("artifact path must be text");
    let expected = record["sha256"]
        .as_str()
        .expect("artifact sha256 must be text");
    let path = project_path(relative);
    assert_eq!(
        sha256(&path),
        expected,
        "stale extraction artifact {relative}"
    );
}

#[test]
fn obligation_kernel_transition_model_is_source_bound_and_explicitly_conditional() {
    let extraction: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/obligation-kernel/extraction.json",
        ))
        .unwrap(),
    )
    .unwrap();

    assert_eq!(
        extraction["status"],
        "source-hash-bound-and-conditionally-refinement-proved"
    );
    assert_eq!(extraction["counts_as_implementation_refinement"], true);
    assert_eq!(extraction["extraction"]["direct_production_source"], true);
    assert_eq!(
        extraction["extraction"]["mechanical_rust_extraction"],
        false
    );
    assert_eq!(
        extraction["extraction"]["source_correspondence_premise"],
        "ObligationKernel.Corresponds"
    );
    assert_eq!(extraction["extraction"]["premise_discharged"], false);
    assert_recorded_hash(&extraction["source"]);
    for generated in extraction["generated"].as_array().unwrap() {
        assert_recorded_hash(generated);
    }
    for proof in extraction["proof_project"].as_array().unwrap() {
        assert_recorded_hash(proof);
    }
    assert_eq!(
        extraction["proof_progress"]["consume_produce_close_semantics_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["decision_determinism_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["source_correspondence_conditional"],
        true
    );
    assert_eq!(extraction["open_obligations"].as_array().unwrap().len(), 1);
}

#[test]
fn full_bind_call_translation_has_a_public_all_input_refinement_proof() {
    let extraction: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/call-binding-full/extraction.json",
        ))
        .unwrap(),
    )
    .unwrap();

    assert_eq!(
        extraction["status"],
        "translated-compiled-and-universally-refinement-proved"
    );
    assert_eq!(extraction["counts_as_implementation_refinement"], true);
    assert_eq!(
        extraction["source"]["entrypoint"],
        "bind_call_with_allocator"
    );
    assert_eq!(extraction["source"]["production_wrapper"], "bind_call");
    assert_eq!(extraction["source"]["arbitrary_argument_cap"], false);
    assert_eq!(
        extraction["source"]["count_overflow_semantics"],
        "checked-usize-with-phase-specific-typed-errors"
    );
    assert_recorded_hash(&extraction["source"]);
    assert_recorded_hash(&extraction["manifest"]);
    for generated in extraction["generated"].as_array().unwrap() {
        assert_recorded_hash(generated);
    }
    for external in extraction["external_models"].as_array().unwrap() {
        assert_recorded_hash(external);
        assert_eq!(external["trusted"], false);
        assert!(
            external["constructive"] == true
                || external["unconditional_helper_proofs_depend_on_model"] == false,
            "a nonconstructive external boundary must be excluded by the helper theorem dependency audits"
        );
    }
    for proof_artifact in extraction["proof_project"].as_array().unwrap() {
        assert_recorded_hash(proof_artifact);
    }
    assert_eq!(extraction["proof_progress"]["generated_loops"], 28);
    assert_eq!(extraction["proof_progress"]["remaining_generated_loops"], 0);
    assert_eq!(
        extraction["proof_progress"]["generated_loops_proved"]
            .as_array()
            .unwrap()
            .len(),
        28
    );
    let checked_theorems = extraction["proof_progress"]["checked_theorems"]
        .as_array()
        .unwrap();
    for theorem in [
        "BindCallFull.Proofs.bind_call_with_allocator_matches_exact_reference",
        "BindCallFull.Proofs.bindingResultView_injective",
        "BindCallFull.Proofs.expand_actual_items_with_allocator_matches_reference",
        "BindCallFull.Proofs.validate_signature_matches_reference",
    ] {
        assert!(checked_theorems.iter().any(|checked| checked == theorem));
    }
    for audit in extraction["axiom_audits"].as_array().unwrap() {
        assert_eq!(audit["contains_sorry_ax"], false);
    }
    assert_eq!(extraction["open_obligations"], serde_json::json!([]));
    assert_eq!(
        extraction["external_contracts"][0]["boundary"],
        "SystemBindingAllocator::allocate"
    );
    assert_eq!(
        extraction["external_contracts"][0]["included_in_proved_binder_semantics"],
        false
    );

    let translation: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/call-binding-full/generated/translation.json",
        ))
        .unwrap(),
    )
    .unwrap();
    let bind_call = translation["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["lean_name"] == "BindCallFull.bind_call_with_allocator")
        .expect("full extraction must contain bind_call_with_allocator");
    assert_eq!(bind_call["is_local"], true);
    assert_eq!(bind_call["is_opaque"], false);
    assert_eq!(
        bind_call["source"]["begin_line"],
        extraction["source"]["line_start"]
    );
    assert_eq!(
        bind_call["source"]["end_line"],
        extraction["source"]["line_end"]
    );
}

#[test]
fn vc_term_sort_translation_is_source_bound_constructive_and_exactly_refined() {
    let extraction: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/vc-term-sort/extraction.json",
        ))
        .unwrap(),
    )
    .unwrap();

    assert_eq!(
        extraction["status"],
        "translated-compiled-exact-structured-all-input-refinement-proved"
    );
    assert_eq!(extraction["counts_as_implementation_refinement"], true);
    assert_eq!(
        extraction["source"]["entrypoint"],
        "term_sort_extraction_entrypoint"
    );
    assert_eq!(
        extraction["source"]["production_method"],
        "Term::sort_typed"
    );
    assert_eq!(extraction["source"]["mounted_as_hard_link"], true);
    assert_eq!(extraction["source"]["sort_variants"], 16);
    assert_eq!(extraction["source"]["term_variants"], 68);
    assert_eq!(extraction["toolchain"]["container_used"], true);
    assert_eq!(
        extraction["translation"]["transparent_local_definitions"],
        59
    );
    assert_eq!(extraction["translation"]["entrypoint_transparent"], true);
    assert_eq!(extraction["translation"]["term_sort_transparent"], true);
    assert_eq!(
        extraction["translation"]["normalization_correspondence_proved"],
        true
    );
    assert_eq!(
        extraction["translation"]["normalized_finite_slice_loops"],
        15
    );
    assert_eq!(
        extraction["proof_progress"]["top_level_obligations_closed"],
        8
    );
    assert_eq!(
        extraction["proof_progress"]["top_level_obligations_total"],
        8
    );
    assert_eq!(
        extraction["proof_progress"]["all_input_entrypoint_refinement_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["all_input_entrypoint_termination_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["wrapper_decomposition_proved"],
        true
    );
    assert_eq!(extraction["proof_progress"]["sort_clone_model_exact"], true);
    assert_eq!(
        extraction["proof_progress"]["sort_structural_equality_model_exact"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["compiler_derived_trait_correspondence_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["recursive_storage_measure_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["nonrecursive_constructor_termination_proved"],
        10
    );
    assert_eq!(
        extraction["proof_progress"]["recursive_constructor_termination_proved"],
        58
    );
    assert_eq!(
        extraction["proof_progress"]["recursive_constructor_termination_total"],
        58
    );
    assert_eq!(
        extraction["proof_progress"]["model_vec_observation_lemmas_proved"],
        4
    );
    assert_eq!(
        extraction["proof_progress"]["model_vec_push_refinement_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["recursive_vec_list_refinement_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["standard_library_model_refinement_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["generic_finite_loop_trace_semantics_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["concrete_loop_trace_bounds_proved"],
        15
    );
    assert_eq!(
        extraction["proof_progress"]["concrete_loop_trace_bounds_total"],
        15
    );
    assert_eq!(
        extraction["proof_progress"]["concrete_loop_bounds_composed"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["finite_loop_runner_refinement_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["checked_theorem_declarations"],
        520
    );
    assert_eq!(
        extraction["proof_progress"]["raw_recursive_constructor_termination_proved"],
        extraction["proof_progress"]["raw_recursive_constructor_termination_total"]
    );
    assert_eq!(
        extraction["proof_progress"]["raw_normalization_constructor_correspondence_proved"],
        extraction["proof_progress"]["raw_normalization_constructor_correspondence_total"]
    );
    assert_eq!(
        extraction["proof_progress"]["raw_entrypoint_correspondence_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["structured_success_error_field_correspondence_proved"],
        true
    );
    assert_eq!(
        extraction["proof_progress"]["axiom_dependency_audited"],
        true
    );
    assert_eq!(extraction["lean_build"]["result"], "passed");
    assert_eq!(extraction["lean_build"]["jobs"], 1719);
    assert_eq!(
        extraction["lean_build"]["public_theorem"],
        "VcTermSort.Proofs.raw_term_sort_extraction_entrypoint_structured_refinement"
    );

    assert_recorded_hash(&extraction["source"]);
    assert_recorded_hash(&extraction["manifest"]);
    for generated in extraction["generated"].as_array().unwrap() {
        assert_recorded_hash(generated);
    }
    for external in extraction["external_models"].as_array().unwrap() {
        assert_recorded_hash(external);
        assert_eq!(external["constructive"], true);
        assert_eq!(external["trusted"], false);
    }
    for project_file in extraction["proof_project"].as_array().unwrap() {
        assert_recorded_hash(project_file);
    }
    assert!(
        extraction["open_obligations"]
            .as_array()
            .unwrap()
            .is_empty()
    );

    let translation: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/vc-term-sort/generated/translation.json",
        ))
        .unwrap(),
    )
    .unwrap();
    for lean_name in [
        "VcTermSort.Term.sort_typed",
        "VcTermSort.term_sort_extraction_entrypoint",
    ] {
        let function = translation["functions"]
            .as_array()
            .unwrap()
            .iter()
            .find(|function| function["lean_name"] == lean_name)
            .unwrap_or_else(|| panic!("missing transparent extraction for {lean_name}"));
        assert_eq!(function["is_local"], true);
        assert_eq!(function["is_opaque"], false);
    }
}

#[test]
fn io_sort_kernel_translation_is_source_bound_total_and_exactly_refined() {
    let extraction: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/io-sort-kernel/extraction.json",
        ))
        .unwrap(),
    )
    .unwrap();

    assert_eq!(
        extraction["status"],
        "translated-compiled-and-universally-refinement-proved"
    );
    assert_eq!(extraction["counts_as_implementation_refinement"], true);
    assert_eq!(extraction["source"]["value_variants"], 3);
    assert_eq!(extraction["source"]["sort_variants"], 2);
    assert_eq!(
        extraction["source"]["payloads_ignored_only_after_constructor_match"],
        true
    );
    let source_functions = extraction["source"]["functions"].as_array().unwrap();
    assert_eq!(source_functions.len(), 2);
    for name in ["same_value_sort", "value_has_sort"] {
        assert!(
            source_functions
                .iter()
                .any(|function| function["name"] == name),
            "missing source-bound IO sort function {name}"
        );
    }

    assert_recorded_hash(&extraction["source"]);
    assert_recorded_hash(&extraction["manifest"]);
    assert_recorded_hash(&extraction["lockfile"]);
    for generated in extraction["generated"].as_array().unwrap() {
        assert_recorded_hash(generated);
    }
    for project_file in extraction["proof_project"].as_array().unwrap() {
        assert_recorded_hash(project_file);
    }

    assert_eq!(extraction["external_models"], serde_json::json!([]));
    assert_eq!(extraction["translation"]["local_functions"], 2);
    assert_eq!(extraction["translation"]["transparent_local_functions"], 2);
    assert_eq!(extraction["translation"]["opaque_functions"], 0);
    assert_eq!(extraction["translation"]["recursive_functions"], 0);
    assert_eq!(extraction["translation"]["can_diverge_functions"], 0);
    assert_eq!(extraction["lean_build"]["result"], "passed");
    assert_eq!(extraction["lean_build"]["jobs"], 1704);

    for field in [
        "all_input_value_has_sort_refinement_proved",
        "all_input_same_value_sort_refinement_proved",
        "all_input_value_has_sort_totality_proved",
        "all_input_same_value_sort_totality_proved",
    ] {
        assert_eq!(extraction["proof_progress"][field], true);
    }
    assert_eq!(
        extraction["proof_progress"]["value_has_sort_constructor_cases"],
        6
    );
    assert_eq!(
        extraction["proof_progress"]["same_value_sort_constructor_cases"],
        9
    );
    assert_eq!(extraction["open_obligations"], serde_json::json!([]));

    for audit in extraction["axiom_audits"].as_array().unwrap() {
        assert_eq!(audit["axioms"], serde_json::json!(["propext"]));
        assert_eq!(audit["contains_sorry_ax"], false);
    }

    let translation: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/io-sort-kernel/generated/translation.json",
        ))
        .unwrap(),
    )
    .unwrap();
    let translated_functions = translation["functions"].as_array().unwrap();
    assert_eq!(translated_functions.len(), 2);
    for source_function in source_functions {
        let name = source_function["name"].as_str().unwrap();
        let rust_name = format!("maledictus::python_io_contracts::{name}");
        let translated = translated_functions
            .iter()
            .find(|function| function["rust_name"] == rust_name)
            .unwrap_or_else(|| panic!("missing generated translation for {rust_name}"));
        assert_eq!(translated["is_local"], true);
        assert_eq!(translated["is_opaque"], false);
        assert_eq!(translated["can_diverge"], false);
        assert_eq!(
            translated["source"]["begin_line"],
            source_function["line_start"]
        );
        assert_eq!(
            translated["source"]["end_line"],
            source_function["line_end"]
        );
    }
}

#[test]
fn persistent_collection_translation_records_exact_proved_and_open_kernels() {
    let extraction: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/persistent-collections/extraction.json",
        ))
        .unwrap(),
    )
    .unwrap();

    assert_eq!(
        extraction["status"],
        "four-kernels-extracted-three-kernels-universally-refinement-proved"
    );
    assert_eq!(extraction["counts_as_implementation_refinement"], true);
    assert_recorded_hash(&extraction["source"]);
    assert_recorded_hash(&extraction["manifest"]);
    assert_recorded_hash(&extraction["lockfile"]);
    for generated in extraction["generated"].as_array().unwrap() {
        assert_recorded_hash(generated);
    }
    for proof_artifact in extraction["proof_project"].as_array().unwrap() {
        assert_recorded_hash(proof_artifact);
    }

    let functions = extraction["source"]["extracted_functions"]
        .as_array()
        .unwrap();
    assert_eq!(functions.len(), 4);
    for proved in [
        "require_compatible_kinds_typed",
        "concatenate_typed",
        "unique",
    ] {
        let function = functions
            .iter()
            .find(|function| function["name"] == proved)
            .unwrap_or_else(|| panic!("missing extracted persistent kernel {proved}"));
        assert_eq!(function["universally_proved"], true);
    }
    let open = "comparable_equal_typed";
    let function = functions
        .iter()
        .find(|function| function["name"] == open)
        .unwrap_or_else(|| panic!("missing extracted persistent kernel {open}"));
    assert_eq!(function["universally_proved"], false);
    assert_eq!(extraction["proof_progress"]["requested_kernels"], 4);
    assert_eq!(
        extraction["proof_progress"]["universally_proved_kernels"],
        3
    );
    assert_eq!(
        extraction["proof_progress"]["open_kernels"],
        serde_json::json!(["comparable_equal_typed"])
    );
    for audit in extraction["axiom_audits"].as_array().unwrap() {
        assert_eq!(audit["contains_sorry_ax"], false);
    }
}

#[test]
fn kernel_exit_effects_translation_is_direct_constructive_and_exactly_refined() {
    let extraction: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/kernel-exit-effects/extraction.json",
        ))
        .unwrap(),
    )
    .unwrap();

    assert_eq!(
        extraction["status"],
        "translated-compiled-and-universally-refinement-proved"
    );
    assert_eq!(extraction["counts_as_implementation_refinement"], true);
    assert_eq!(extraction["source"]["path"], "src/kernel.rs");
    assert_eq!(extraction["extraction"]["direct_production_source"], true);
    assert_eq!(extraction["extraction"]["rust_wrapper"], false);
    assert_eq!(extraction["extraction"]["source_seam"], false);

    assert_recorded_hash(&extraction["source"]);
    assert_recorded_hash(&extraction["manifest"]);
    assert_recorded_hash(&extraction["lockfile"]);
    for artifact in extraction["generated"].as_array().unwrap() {
        assert_recorded_hash(artifact);
    }
    for external in extraction["external_models"].as_array().unwrap() {
        assert_recorded_hash(external);
        assert_eq!(external["constructive"], true);
        assert_eq!(external["trusted"], false);
    }
    for artifact in extraction["proof_project"].as_array().unwrap() {
        assert_recorded_hash(artifact);
    }

    let function = &extraction["source"]["extracted_functions"][0];
    assert_eq!(function["name"], "check_exit_effects");
    assert_eq!(function["universally_proved"], true);
    assert_eq!(
        extraction["lean_build"]["public_theorem"],
        "KernelExitEffects.Proofs.check_exit_effects_all_inputs_exact"
    );
    assert_eq!(extraction["proof_progress"]["open_obligations"], 0);
    assert_eq!(extraction["open_obligations"], serde_json::json!([]));
    assert_eq!(
        extraction["axiom_audits"][0]["axioms"],
        serde_json::json!(["propext", "Classical.choice", "Quot.sound"])
    );
    assert_eq!(extraction["axiom_audits"][0]["contains_sorry_ax"], false);
}

#[test]
fn solver_sort_predicate_translation_is_direct_constructive_and_exactly_refined() {
    let extraction: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/solver-sort-predicates/extraction.json",
        ))
        .unwrap(),
    )
    .unwrap();

    assert_eq!(
        extraction["status"],
        "translated-compiled-and-universally-refinement-proved"
    );
    assert_eq!(extraction["counts_as_implementation_refinement"], true);
    assert_eq!(extraction["source"]["path"], "src/solver.rs");
    assert_eq!(extraction["extraction"]["direct_production_source"], true);
    assert_eq!(extraction["extraction"]["rust_wrapper"], false);
    assert_eq!(extraction["extraction"]["source_seam"], false);

    assert_recorded_hash(&extraction["source"]);
    for artifact in extraction["generated"].as_array().unwrap() {
        assert_recorded_hash(artifact);
    }
    for external in extraction["external_models"].as_array().unwrap() {
        assert_recorded_hash(external);
        assert_eq!(external["constructive"], true);
        assert_eq!(external["trusted"], false);
    }
    for artifact in extraction["proof_project"].as_array().unwrap() {
        assert_recorded_hash(artifact);
    }

    let functions = extraction["source"]["extracted_functions"]
        .as_array()
        .unwrap();
    for expected in [
        "is_z3_collection_key_sort",
        "is_z3_collection_value_sort",
        "is_z3_nested_equality_sort",
    ] {
        let function = functions
            .iter()
            .find(|function| function["name"] == expected)
            .unwrap_or_else(|| panic!("missing extracted solver-sort predicate {expected}"));
        assert_eq!(function["universally_proved"], true);
    }
    assert_eq!(extraction["proof_progress"]["open_obligations"], 0);
    assert_eq!(extraction["open_obligations"], serde_json::json!([]));
    for audit in extraction["axiom_audits"].as_array().unwrap() {
        assert_eq!(
            audit["axioms"],
            serde_json::json!(["propext", "Classical.choice", "Quot.sound"])
        );
        assert_eq!(audit["contains_sorry_ax"], false);
    }
}

#[test]
fn solver_adjacent_order_translation_is_direct_constructive_and_exactly_refined() {
    let extraction: serde_json::Value = serde_json::from_slice(
        &fs::read(project_path(
            "formal/extraction/solver-adjacent-order/extraction.json",
        ))
        .unwrap(),
    )
    .unwrap();

    assert_eq!(
        extraction["status"],
        "translated-compiled-and-universally-refinement-proved"
    );
    assert_eq!(extraction["counts_as_implementation_refinement"], true);
    assert_eq!(extraction["source"]["path"], "src/solver.rs");
    assert_eq!(extraction["extraction"]["direct_production_source"], true);
    assert_eq!(extraction["extraction"]["rust_wrapper"], false);
    assert_eq!(extraction["extraction"]["source_seam"], false);

    assert_recorded_hash(&extraction["source"]);
    for artifact in extraction["generated"].as_array().unwrap() {
        assert_recorded_hash(artifact);
    }
    for external in extraction["external_models"].as_array().unwrap() {
        assert_recorded_hash(external);
        assert_eq!(external["constructive"], true);
        assert_eq!(external["trusted"], false);
    }
    for artifact in extraction["proof_project"].as_array().unwrap() {
        assert_recorded_hash(artifact);
    }

    let functions = extraction["source"]["extracted_functions"]
        .as_array()
        .unwrap();
    for expected in [
        "is_exact_sorted_adjacent_order_theorem",
        "unwrap_singleton_and",
        "is_bound_variable",
        "is_integer_literal",
        "is_bound_successor",
        "is_python_index_of",
        "is_nonnegative_bound",
        "is_adjacent_upper_bound",
    ] {
        let function = functions
            .iter()
            .find(|function| function["name"] == expected)
            .unwrap_or_else(|| panic!("missing extracted adjacent-order function {expected}"));
        assert_eq!(function["universally_proved"], true);
    }
    assert_eq!(extraction["proof_progress"]["open_obligations"], 0);
    assert_eq!(extraction["open_obligations"], serde_json::json!([]));
    for audit in extraction["axiom_audits"].as_array().unwrap() {
        let theorem = audit["theorem"].as_str().unwrap();
        let expected_axioms = if theorem.ends_with("is_integer_literal_all_inputs_exact")
            || theorem.ends_with("is_bound_variable_all_inputs_exact")
        {
            serde_json::json!(["propext", "Quot.sound"])
        } else {
            serde_json::json!(["propext", "Classical.choice", "Quot.sound"])
        };
        assert_eq!(audit["axioms"], expected_axioms);
        assert_eq!(audit["contains_sorry_ax"], false);
    }
}
