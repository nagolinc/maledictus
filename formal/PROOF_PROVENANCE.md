# Implementation-proof provenance

An existing Lean build is not evidence that its extracted program still matches
the current Rust program. The release coverage check validates exact source and
artifact bytes before it counts a source-bound theorem.

## Extracted source closure

Mechanical extraction manifests name their primary `source.path` and any
`source_dependencies`. Each dependency has a repository-relative `path` and an
exact `sha256`. Dependency paths must resolve to files inside the repository,
including after following filesystem links.

The checker reads each sealed Aeneas translation inventory. Every local function,
type, global, trait declaration and trait implementation must have a source origin
covered by the primary source or a dependency. Removing the dependency list does
not remove the obligation: the compiler inventory still requires it.

Standalone extraction projects sometimes expose a real source file under another
path. `extracted_paths` records those exact compiler spellings. For example, the
VC extraction workspace verifies that `src/lib.rs` is a hard link to the actual
`src/vc.rs`. No basename matching or implicit path substitution is performed.
The provenance records the extraction route; the inventory check does not itself
prove a compiler correct or retrospectively recreate an old extraction mount.

An unconditional source-refinement classification requires a sealed extraction
inventory. The older obligation-transition proof remains explicitly conditional
on its source-correspondence premise; it is not reclassified as a mechanically
extracted proof because it has no inventory.

## Source transformations are proof obligations

The VC and solver extractions retain their raw generated functions. Where finite
source loops are represented by fuel-bounded Lean functions, constructive
correspondence theorems connect the actual partial loops to the finite runners.
The fuel comes from a decreasing source-state measure, not an arbitrary cap.

Coverage entries for the solver predicates and adjacent-order recognizer point
directly to specification theorems about the raw extracted functions. Their
normalization equalities are separately checked. Updating a source digest without
regenerating the program and discharging these obligations is not a repair.

The VC extraction explicitly models compiler-derived Term cloning after the
extractor refuses its recursive trait component. An independent structural clone
definition reconstructs all 69 constructors and recursive storage; its identity
and model-correspondence theorems are checked. This establishes immutable value
equality, not allocation-failure, execution-time, or application exception claims.

## What these proofs do not establish

These are particular implementation refinements, not a proof of the entire
verifier, its frontends, the compiler/extractor, native libraries, or an application.
The package checks and application tests remain distinct evidence. Application
timing claims still require actual worker bindings and explicit production,
resource, refill, and platform premises.

Raw byte hashes are not normalized by the checker. The repository's attributes
pin proof-sensitive text to LF, and release checks use the exact committed tree.
Both positive axiom audits and deliberately invalid `sorryAx`/project-axiom
controls must behave correctly. An expected failing child is test data; it must
not leak an error exit code into a successful CI wrapper, and an unexpectedly
passing or unrelated failing child must still make that wrapper fail.
