# Obligation ledger transition proof

This project proves the AST-independent transition algebra used by
src/obligation_kernel.rs: exact measure sufficiency, positive bounded countdown transfer,
collision-preserving production, presence/measure/policy-checked consumption, exact bounded loop
invariant preservation, boundary closure, and deterministic decisions.

The Rust analyzer resolves Python identities and commits map mutations. Those frontend and map
correspondence steps are deliberately outside this theorem. The checked source hash links the
model to the exact Rust kernel, while `Corresponds` remains an explicit premise. Formal coverage
therefore classifies these functions as conditional source-bound—not unconditional—until a
mechanical Rust extraction discharges that premise.

The positive axiom audit admits no axioms. Both negative fixtures must reject `sorryAx` and a
project-owned axiom.
