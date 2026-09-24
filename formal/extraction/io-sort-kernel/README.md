# Production IO sort-kernel extraction

This artifact source-binds the two primitive type judgments used by the production linear IO
executor in `src/python_io_contracts.rs`:

- `value_has_sort`, which checks a wrapper argument against its declared IO sort; and
- `same_value_sort`, which checks whether a provider equality can unify two values.

The extraction manifest compiles the real production library through `../../../src/lib.rs`; it
does not contain a copied Rust implementation or a proof-only classifier. Charon selects the two
private source functions directly. Both generated Lean definitions are transparent, total, and
have no external function models.

`IoSortKernel.Proofs.value_has_sort_matches_reference` and
`IoSortKernel.Proofs.same_value_sort_matches_reference` prove exact correspondence for every
constructor and payload of `Value` and `IoSort`. The two totality theorems additionally rule out
generated failure or divergence for all inputs. The axiom audit requires all four public theorems
to depend on exactly Lean's standard propositional extensionality axiom and rejects `sorryAx` or
any project-owned axiom.

The pinned extraction commands, run from this directory, are:

```text
charon cargo --preset=aeneas \
  --start-from crate::python_io_contracts::value_has_sort \
  --start-from crate::python_io_contracts::same_value_sort \
  --error-on-warnings --dest-file=io_sort.llbc -- --offline --lib

aeneas -backend lean -namespace IoSortKernel -subdir IoSortKernel/Code \
  -split-files -emit-json -abort-on-error -dest generated io_sort.llbc
```

The checked proof and audit commands are:

```text
powershell.exe -NoProfile -ExecutionPolicy Bypass -File ../../run-lake.ps1 \
  -Project io-sort-kernel -LakePath lake build IoSortKernelProofs
powershell.exe -NoProfile -ExecutionPolicy Bypass -File ../../run-lake.ps1 \
  -Project io-sort-kernel -LakePath lake env lean proofs/IoSortKernelProofs/AxiomAudit.lean
cargo test --lib io_sort_predicates_and_diagnostics_cover_every_value_class
cargo test --test rust_lean_extraction_artifacts
```
