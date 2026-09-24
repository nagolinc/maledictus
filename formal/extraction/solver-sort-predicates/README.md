# Solver sort-predicate extraction

This project proves the three production predicates `is_z3_collection_key_sort`,
`is_z3_collection_value_sort`, and `is_z3_nested_equality_sort` directly from
`src/solver.rs`. Charon roots those real functions in the main crate; there is no Rust wrapper,
proof-only source seam, or modeled replacement for a production function.

Using the repository's pinned Ubuntu toolchain, run Charon with preset `aeneas`,
`--error-on-warnings`, and these three `--start-from` roots:

```text
crate::solver::is_z3_collection_key_sort
crate::solver::is_z3_collection_value_sort
crate::solver::is_z3_nested_equality_sort
```

Translate the resulting LLBC with the pinned Aeneas release using backend `lean`, namespace
`SolverSortPredicates`, `-split-files`, `-emit-json`, `-abort-on-error`, and `-loops-no-rec`.
Then run `normalize-generated.ps1`. The normalizer fails closed unless it sees the one recursive
`Vec<Sort>` representation and the three generated source-loop calls. It maps the recursive Vec
to Lean's strictly-positive `List`, and replaces each Aeneas partial-loop primitive with the exact
finite iterator fuel `remaining length + 1`. `FunsExternal.lean` constructively realizes the only
opaque external call, shared Vec iteration, as the same bounded list prefix.

The three public exactness theorems quantify over every normalized `Sort`. The positive axiom
audit fixes the exact dependency set, while both negative fixtures must reject `sorryAx` and a
project-owned axiom.
