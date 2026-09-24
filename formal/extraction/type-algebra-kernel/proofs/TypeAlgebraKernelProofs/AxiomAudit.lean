import TypeAlgebraKernelProofs.Refinement
import TypeAlgebraKernelProofs.NominalFromVec
import TypeAlgebraKernelProofs.HierarchyConstruction
import Lean.Util.CollectAxioms

open Lean Lean.Elab Lean.Elab.Command

namespace TypeAlgebraKernel.AxiomAudit

def exactAxiomSet (actual expected : Array Name) : Bool :=
  actual.qsort Name.lt == expected.qsort Name.lt

def assertExactAxioms (declaration : Name) (expected : Array Name) : CommandElabM Unit := do
  let actual <- Lean.collectAxioms declaration
  if !exactAxiomSet actual expected then
    throwError
      "axiom audit failed for '{declaration}': expected exactly {expected.qsort Name.lt |>.toList}, got {actual.qsort Name.lt |>.toList}"

def structuralAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

def nominalAxioms : Array Name :=
  structuralAxioms ++ #[
    `TypeAlgebraKernel.Proofs.is_subclass_exact._native.decide.ax_1_6,
    `TypeAlgebraKernel.Proofs.is_subclass_exact._native.decide.ax_1_7,
    `TypeAlgebraKernel.Proofs.is_subclass_exact._native.decide.ax_1_9,
    `TypeAlgebraKernel.Proofs.subclassDecisionAllReference._native.decide.ax_1,
    `TypeAlgebraKernel.python_type_algebra_kernel.is_subclass._native.decide.ax_1
  ]

def allInputNominalAxioms : Array Name :=
  structuralAxioms ++ #[
    `TypeAlgebraKernel.Proofs.is_subclass_all_inputs_exact._native.decide.ax_1_5,
    `TypeAlgebraKernel.Proofs.is_subclass_all_inputs_exact._native.decide.ax_1_6,
    `TypeAlgebraKernel.Proofs.is_subclass_all_inputs_exact._native.decide.ax_1_8,
    `TypeAlgebraKernel.Proofs.subclassDecisionAllReference._native.decide.ax_1,
    `TypeAlgebraKernel.python_type_algebra_kernel.is_subclass._native.decide.ax_1
  ]

def hierarchyConstructionAxioms : Array Name :=
  structuralAxioms ++ #[
    `TypeAlgebraHierarchy.python_type_algebra_kernel.validate_nominal_hierarchy._native.decide.ax_1,
    `TypeAlgebraKernel.Proofs.NominalConstruction.object_name_from_str_exact._native.decide.ax_1,
    `TypeAlgebraKernel.Proofs.NominalConstruction.object_name_from_str_exact._native.decide.ax_1_1,
    `TypeAlgebraKernel.Proofs.NominalConstruction.object_name_from_str_exact._native.native_decide.ax_1_4
  ]

#guard !exactAxiomSet #[Name.mkSimple ("sorr" ++ "yAx")] nominalAxioms
#guard !exactAxiomSet
  (nominalAxioms ++ #[`Maledictus.unexpectedAxiom]) nominalAxioms

end TypeAlgebraKernel.AxiomAudit

open TypeAlgebraKernel.AxiomAudit

run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.normalize_union_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.expand_union_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.clone_type_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.clone_type_list_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.type_equals_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.type_lists_equal_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.type_list_contains_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.flatten_union_types_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.reverse_type_list_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.normalize_type_list_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.expand_union_list_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.nominal_class_list_len_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.typeList_into_vec_all_inputs_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.typeList_from_vec_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.nominalClassList_from_vec_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.class_parent_all_inputs_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.subclass_with_remaining_all_inputs_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.type_is_well_formed_all_inputs_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.type_list_is_well_formed_all_inputs_exact structuralAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.is_subclass_all_inputs_exact allInputNominalAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.is_assignable_in_valid_hierarchy_all_inputs_exact allInputNominalAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.every_type_assignable_to_all_inputs_exact allInputNominalAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.type_assignable_to_any_all_inputs_exact allInputNominalAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.type_lists_assignable_all_inputs_exact allInputNominalAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.is_assignable_all_inputs_exact allInputNominalAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.narrow_variants_all_inputs_exact allInputNominalAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.cast_compatible_exact nominalAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.narrow_type_exact nominalAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.NominalConstruction.validate_nominal_hierarchy_all_inputs_exact hierarchyConstructionAxioms
run_cmd assertExactAxioms ``TypeAlgebraKernel.Proofs.NominalConstruction.build_nominal_hierarchy_all_inputs_exact hierarchyConstructionAxioms
