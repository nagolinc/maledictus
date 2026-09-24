# Solver adjacent-order extraction

This project proves the production adjacent-order recognizer and its seven directly called
predicates from `src/solver.rs`. Charon roots the real
`is_exact_sorted_adjacent_order_theorem` function in the main crate; there is no Rust wrapper,
proof-only source seam, or modeled replacement for any covered production function.

Using the repository's pinned Ubuntu toolchain, run Charon with preset `aeneas`,
`--error-on-warnings`, and root
`crate::solver::is_exact_sorted_adjacent_order_theorem`. The production `Term` equality
implementation is deliberately opaque at the extraction boundary and is realized
constructively by the same structural equality in `FunsExternal.lean`.

Translate the LLBC with the pinned Aeneas release using backend `lean`, namespace
`SolverAdjacentOrder`, `-split-files`, `-emit-json`, `-abort-on-error`, and `-loops-no-rec`.
Then run `normalize-generated.ps1`. The normalizer fails closed unless it sees exactly sixteen
recursive `Vec` type occurrences, three generated `Vec` operations, and the one generated source
loop. It maps recursive vectors to Lean's strictly-positive `List`, maps the three vector
operations to constructive list models, and replaces Aeneas's partial loop primitive with the
exact structural fuel `sizeOf term + 1`.

The eight public exactness theorems quantify over every normalized input. The positive axiom
audit fixes each theorem's exact dependency set, while both negative fixtures must reject
`sorryAx` and a project-owned axiom.
