# Production `Term::sort` extraction

This project contains a source-bound Charon/Aeneas translation of the production
`src/vc.rs::Term::sort` type kernel. The extraction crate hard-links that file as
`src/lib.rs`; it does not contain a proof-only copy or a second type checker. A transparent
source wrapper exists only because pinned Charon cannot select an inherent method with
`--start-from`. The generated wrapper calls the generated `Term.sort_typed` directly.

The exact local extraction closure contains 59 transparent definitions, including the full
`Term.sort_typed`, all reachable source helpers and loop bodies, all 68 `Term` constructors, and all
16 `Sort` constructors. Compiler-generated `Sort` clone, equality, and debug functions are
opaque at the Charon boundary because Aeneas cannot emit their recursive implementations in a
Lean-valid order. `FunsExternal.lean` gives them constructive structural definitions; it does not
assert axioms.

`ListSlice` stores an optional literal lower bound, optional literal upper bound, and a
`NonZeroI128` step. The sort kernel observes only the recursive source term, so the constructive
Lean model preserves the integer payload and proves the branch for every modeled value (including
zero); it does not assume the Rust constructor invariant.

## Reproduction boundary

Create the disposable extraction crate from the repository root before invoking Charon:

```powershell
powershell -ExecutionPolicy Bypass -File `
  formal/extraction/vc-term-sort/setup-extraction-workspace.ps1
```

The setup is idempotent. It copies the checked-in extraction `Cargo.toml` into
`.cache/vc-term-sort-extraction`, hard-links `src/vc.rs` as that crate's `src/lib.rs`, and then
validates both files. It fails instead of overwriting an existing mismatched manifest, copied
source, symbolic link, or hard link to any file other than the production source. Use
`-ValidateOnly` when a command must verify an already-created workspace without changing it.
Disposable Charon, Aeneas, Cargo, and LLBC outputs remain below `.cache/`; they are not inputs to
the checked-in proof project. Run the Charon and Aeneas commands below from
`.cache/vc-term-sort-extraction`; their relative output paths are deliberately cache-local.

The focused setup regression is also self-contained and uses only the operating-system temporary
directory:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File `
  formal/extraction/vc-term-sort/tests/setup-extraction-workspace.Tests.ps1
```

The pinned extraction commands were run inside the recorded Linux container for this refresh:

```text
charon cargo --preset=aeneas \
  --start-from crate::term_sort_extraction_entrypoint \
  --opaque='{impl core::clone::Clone for crate::Sort}' \
  --opaque='{impl core::fmt::Debug for crate::Sort}' \
  --opaque='{impl core::cmp::PartialEq<crate::Sort> for crate::Sort}' \
  --error-on-warnings --dest-file=vc_term_sort.llbc

aeneas -backend lean -namespace VcTermSort -subdir VcTermSort/Code \
  -split-files -emit-json -abort-on-error -loops-no-rec vc_term_sort.llbc

charon cargo --preset=aeneas \
  --start-from 'crate::ObligationResult::satisfied' \
  --error-on-warnings --dest-file=vc_helpers.llbc

powershell -ExecutionPolicy Bypass -File ../../formal/extraction/vc-term-sort/repair-helper-ordered-decls.ps1 \
  -InputPath vc_helpers.llbc -OutputPath vc_helpers_ordered.llbc

aeneas -backend lean -namespace VcTermSort -subdir VcTermSort/Helpers \
  -split-files -emit-json -abort-on-error vc_helpers_ordered.llbc

powershell -ExecutionPolicy Bypass -File normalize-generated.ps1 \
  -RawCodeRoot RAW/VcTermSort/Code \
  -OutputCodeRoot generated/VcTermSort/Code

powershell.exe -NoProfile -ExecutionPolicy Bypass -File ../../run-lake.ps1 \
  -Project vc-term-sort -LakePath lake build VcTermSortProofs
```

The normalization script fails closed on every expected raw replacement count. It makes only
three classes of translation repair:

- recursive Rust `Vec` fields become constructive Lean `List` fields so `Sort` and `Term` are
  strictly positive;
- Aeneas's emitted `String` `PartialOrd.gt` dictionary and constructor-shadowed primitive type
  names are made explicit;
- fifteen finite slice loops call a transparent fuel runner with exactly
  `remaining elements + one exhaustion check`. Their compiler-generated loop bodies are unchanged.

Pinned Charon also emits the transparent `ObligationResult::satisfied` body when it is selected
as an inherent-method root, but omits that focused extraction's declaration order. The helper
repair script fails closed on the exact root, declaration inventory, and transparent body, then
populates only `ordered_decls`; it does not rewrite a declaration or function body. The resulting
Aeneas definition is proved equal to an independent exhaustive match over both source enums.

## Current proof boundary

The proof library constructively establishes four foundational facts for all model inputs:

- the generated extraction wrapper is definitionally equal to generated `Term.sort`;
- the external `Sort.clone` model returns the same immutable recursive value;
- the external recursive `Sort` equality model returns true exactly when its operands are equal;
- bounded vector-model dereference and length observations preserve the complete source list,
  while capacity construction and emptiness have their exact list semantics;
- any finite trace of the normalized loop runner produces the recorded success, failure, or
  divergence result, with arbitrary unused fuel preserving that result.

The reusable decreasing-measure theorem constructs such a trace in at most `measure + 1` body
calls. The generated `all_nominal_references` loop is the first concrete instance: every
continuation advances the actual extracted slice iterator once, and its exact generated wrapper
is proved equal to the bounded trace result. The pair-valued
`all_nominal_reference_keys` loop is proved by the same source-iterator argument. Concrete loop
bounds also cover `validate_int_enum_descriptor`, including every success, failure, and divergence
outcome of its source-bound string and set operations. The `require_predicate_argument_sorts`
loop additionally covers the actual result-state check, recursive `Term.sort`, and diagnostic
allocation outcomes. The `require_permission_transfer_amounts` loop covers its receiver-sort
check, fraction validation, and formatting-model outcomes. Concrete loop bounds are therefore
also established for `require_all_sorts`, using a constructive two-bind continuation lemma that
keeps clone and nested sort-check failure and divergence explicit. Concrete loop bounds are
also established for `collect_sorts`, covering its prior-error short circuit, recursive sort
outcome, and modeled vector-push outcome. The `require_finite_dict_entry_sorts` loop is also
bounded with the extracted key-before-value check order intact: a prior error or a failed or
divergent key check prevents the value check, while every continuing outcome uses the advanced
iterator. The recursive `validate_bound_occurrences.all` loop is bounded as well, retaining the
prior-error short circuit and every outcome of the source-bound recursive term validation while
advancing the extracted iterator exactly once per continuation. Its transfer-specific sibling,
`validate_bound_occurrences.all_transfers`, is bounded with the receiver projection and recursive
validation outcomes intact. The final `validate_bound_occurrences.all_entries` loop preserves
pair destructuring and the generated key-before-value recursive check while advancing once per
continuation. Concrete loop bounds are therefore 15/15.

These facts feed the complete implementation-refinement proof. The normalized and raw termination
proofs cover all 10 nonrecursive and 58 recursive constructors, including `ListSlice` and the
four variadic-tuple constructors,
`ListConcat`, `ListSum`, and `ListSorted`, by strict
source-size induction. `NormalizationCorrespondence` proves constructor correspondence for all
68 constructors and connects the raw generated entrypoint to the normalized program.
`StructuredRefinement` then proves exact success, structured-error field, extraction-failure, and
no-divergence correspondence for every input to the source-bound typed entrypoint.
`VcTermSortProofs.Composition` constructs one typed `ConcreteLoopBounds` proof object containing
all fifteen exact-wrapper bounds, and its `finite_loop_runner_refinement` theorem discharges the
loop-runner obligation.
`VcTermSortProofs.VecRefinement` closes the recursive vec/list obligation with the production
`usize` length invariant and exact results for every vector operation reachable from `Term.sort`:
capacity construction, dereference, length, emptiness, iteration, successful append, and the
maximum-capacity failure.
`VcTermSortProofs.StdlibRefinement` closes the reachable standard-library model obligation with
one typed inventory covering String, slice iteration, Vec, Option, Box, BTreeSet, comparison, and
`must_use`. Every non-callback operation has its exact successful result; callback-parametric
wrappers retain the callback result as an explicit premise, proving that the wrapper introduces
no extra failure or divergence without incorrectly assuming arbitrary callbacks are total.
Diagnostic rendering remains outside the typed kernel claim; compiler-derived `Sort` traits are
proved constructively inside it.
`VcTermSortProofs.DerivedTraits` closes the runtime-bearing compiler-derived `Sort` trait
obligation. Its independent structural clone specification recursively rebuilds every one of the
15 variants and is proved equal to the immutable source value for all inputs. Its independent
derived-equality specification is proved to return the same exact Boolean as the external model.
`Eq` has no runtime method; `Debug` remains deliberately scoped to diagnostic formatting.
`VcTermSortProofs.TerminationMeasure` establishes the well-founded `sizeOf` relation used by
the mutual no-divergence proof. Its exact decrease lemmas cover direct unary and binary
children, list members, optional filter terms, permission-transfer receivers, and both members of
finite-dictionary entry pairs. The raw and normalized recursive proofs connect every generated
mutual call site to that relation and eliminate `.div` for the public extraction entrypoint.
All eight top-level obligations are closed, and this extraction counts as an all-input structured
implementation refinement of `Term::sort_typed`.
The focused helper proof additionally establishes the exact all-input result of
`ObligationResult::satisfied`. The other currently unproved `vc.rs` helpers remain outside this
claim: the serde deserializers require unsupported generic external behavior,
`SortContext::as_str` reaches Aeneas's unsupported static-string bottom, and `SortError::fmt` plus
`Term::sort` cross the external formatting/allocation boundary.
The checked-in project-owned Lean contains no `axiom`, `sorry`, or `admit`; warnings about `sorry`
during Lake builds come from pinned Aeneas library modules, not this project.
