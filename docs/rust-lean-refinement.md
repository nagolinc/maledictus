# Rust-to-Lean refinement plan

## Current proof boundary

The earlier standalone `call_binding::expand_actual_items` implementation-refinement proof has
been superseded because it proves the retired 4096-item policy rather than the current cap-free
production binder. Aeneas now translates the exact source-owned `bind_call_with_allocator`
verification seam used by the production `bind_call` wrapper, including checked machine-size
arithmetic and typed allocation failure sites. Lean proofs cover signature-count arithmetic,
signature validation, allocator behavior, cap-free preflight, expansion, call validation, and
canonical binding. The universal all-input refinement theorem is closed over every allocator
outcome schedule satisfying the source-bound typed allocator contract.

The older 86-case witness and standalone capped extraction are retired historical evidence and do
not support a current capability claim. The source hash, generated files, proof files,
toolchain identities, axiom audits, and exact scope of the current full-binder work are recorded
below `formal/extraction/call-binding-full/`; integrity tests fail if a counted artifact drifts.

The refinement composes preflight, expansion, exact-equality formal-parameter binding, canonical
environment construction, deterministic error precedence, and every modeled allocation transition
through the generated seam. It does not cover Python frontend lowering, the VC type checker, other
type/value specializations, or the rest of Maledictus.

## Exact-source extraction status

[Aeneas](https://github.com/AeneasVerif/aeneas) translates the exact production binder through
Charon LLBC into transparent Lean definitions. This uses a pinned local WSL toolchain, without
Docker or Nix. The LLBC, generated files, source, manifest, and tool hashes are recorded below
`formal/extraction/call-binding-full/`, and the generated modules compile under the pinned Lean
toolchain. The proof project is reproducible from its tracked `lakefile.toml`, `lean-toolchain`,
and `lake-manifest.json`; the manifest pins Aeneas and all transitive Lean dependencies to exact
commits.

All repository Lake commands run through `formal/run-lake.ps1`. The runner stages each workspace
below `.cache/lake/workspaces`, mirrors only the registered source trees, and binds dependency and
build locations to the central `.cache/lake` paths. This is required because Lake otherwise writes
compiled dependency configuration under the source workspace even when `packagesDir` and
`buildDir` are configured elsewhere.

Production no longer imposes an arbitrary argument-count ceiling. Source and expanded counts use
checked machine-size addition; arithmetic overflow is a typed outcome. Each allocation is routed
through a typed allocator boundary that records the exact allocation site and requested size on
failure. The independent Lean reference uses those same checked arithmetic and allocation
transitions rather than assuming that every finite mathematical list fits in physical memory.

Aeneas marks generated iterator loops `can_diverge`. The separate checked loop-specification
modules prove termination on finite slices using `loop.spec_decr_nat` and exact remaining-length
measures, without a fixed application-size cap. They also prove
that the fixed-star loop appends every typed value in exact source order and that the outer loop
produces the exact positional typed-value and named `(String, TypedValue)` sequences for every
finite supported source list (positional, named, and fixed-star actuals), under explicit
identity-clone premises. It also proves the exact left-to-right evaluation-event view, including
source indices, named labels, and fixed-star expansion counts. The positional result theorem is
stronger than payload equality: it proves each explicit/fixed-star origin and exact
source/expansion position in the produced record. The named-record theorem proves the same label,
typed value, and exact evaluation-position correspondence for every named actual. The eventual
public refinement relation connects successful preflight and vector construction to those
loop invariants and covers receiver insertion plus every success/error result. Physical allocation
is not assumed infallible: allocation failure is represented by the same typed outcome in
production and the reference relation.

A concrete `-decreases-clauses` extraction was also attempted against this exact LLBC. Aeneas
generated measure templates for all three loops, but Lean's termination elaborator rejected the
generated monadic `do if` bodies before any user-supplied decreasing tactic could run. Aeneas's Lean
backend rejects `-use-fuel` outright. Consequently neither mode is used to disguise termination.
The checked translation retains the ordinary partial-result loop semantics, and the separate loop
theorems supply termination and exact output invariants for finite slices. Checked arithmetic
theorems cover machine-maximum success and overflow without introducing a smaller policy limit.

## Remaining production-refinement route

The next required milestones are:

1. Extract production `vc::Term::sort`, extend the independent Lean model to every current Rust
   `Sort` and `Term` variant, and prove equivalence plus uniqueness for all finite terms.
2. Establish source-frontend refinement: prove that accepted Python and JavaScript/TypeScript
   frontend descriptors lower to the typed effect/VC graph claimed by the kernel.
3. Extend source-bound extraction and axiom audits to every type/effect rule used for issuance.
4. Only after those proofs compose may capabilities advertise full type-system correctness.

This route still treats Rust-to-LLBC extraction, Aeneas's translator, and external Rust standard
library models as part of the trusted computing base; their versions and hashes must be recorded.
Any handwritten external model must be named explicitly rather than hidden as an ordinary theorem.

## Alternatives considered

- [hax's Lean backend](https://hax.cryspen.com/manual/lean/quick_start/) supports partial extraction,
  but its documentation says the Lean backend is under active development and can fail even for
  otherwise supported Rust. It is a useful fallback experiment, not the first production gate.
- [Creusot](https://creusot.rs/) and [Verus](https://verus-lang.github.io/verus/guide/overview.html)
  can establish universal properties of annotated Rust. They do not directly produce the Lean
  implementation theorem required by this repository, so adopting either would create a second
  proof authority rather than close the existing Rust-to-Lean boundary.
- Generating Rust and Lean from an unverified local schema generator would only move the trusted
  gap into that generator. It is not counted as universal refinement.
