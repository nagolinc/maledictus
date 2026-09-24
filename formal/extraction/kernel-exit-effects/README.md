# Kernel exit-effect extraction

This project extracts `check_exit_effects` directly from `src/kernel.rs`; its Cargo library
target is the production source file, with no proof-only Rust wrapper or source seam.

The checked-in Lean translation is produced by pinned Charon/Aeneas binaries. The three opaque
standard-library calls in the closure are replaced constructively in `FunsExternal.lean`:
slice-iterator `any` is a terminating executable scan, string equality is Lean string equality,
and string clone returns the same immutable Lean string value.

`check_exit_effects_all_inputs_exact` is unconditional over both input slices. Its ordered list
reference returns `NoEffects` for an empty effect list, skips `Return`, skips an allowed `Raise`,
and returns the first disallowed `Raise` or first `Unknown` with the exact source payload.

The positive axiom audit fixes the exact structural dependency set. Both negative fixtures must
fail: one adds `sorryAx`, and the other adds a project-owned axiom.
