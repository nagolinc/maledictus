# Full call-binding extraction

This project extracts the production `src/call_binding.rs::bind_call_with_allocator`
exact-equality verification seam used by the public `bind_call` wrapper, including signature
validation, argument expansion, call validation, deterministic error precedence, and canonical
environment construction. The production source is mounted into the extraction crate as
`src/lib.rs`; there is no proof-only Rust implementation.

The checked translation supersedes the earlier fixed-cap `expand_actual_items` artifact. The full
artifact has independent String/Int reference relations for signature validation, checked-count
preflight, expansion, call validation, and canonical binding. Its public all-input theorem is over
the generated `BindCallFull.bind_call_with_allocator` definition and quantifies over every typed
allocator outcome schedule satisfying the source-bound allocator contract.

The material non-container commands are:

```text
charon cargo --preset=aeneas \
  --start-from crate::bind_call_with_allocator \
  --start-from '{impl core::default::Default for crate::CallSignature}::default' \
  --start-from crate::bind_call_with \
  --error-on-warnings --dest-file=bind_call_full_v3.llbc
aeneas -backend lean -namespace BindCallFull -subdir BindCallFull/Code \
  -split-files -emit-json -abort-on-error bind_call_full_v3.llbc
powershell.exe -NoProfile -ExecutionPolicy Bypass -File ../../run-lake.ps1 \
  -Project call-binding-full -LakePath lake build BindCallFull
```

The `bind_call_with` root is present to reach the callback compatibility implementation through a
normal production call graph; the `Default` trait implementation is a supported direct Charon
root. Charon 0.1.245 does not support inherent implementations as `--start-from` roots, so the
constructor helpers are intentionally not claimed by this artifact.

The pinned Aeneas release emits the system allocator's polymorphic trait field with an explicit
type binder and omits the inferred result type at its sole `allocate_buffer` call. The checked
`Funs.lean` applies the proof-preserving elaboration corrections `fun (T : Type)` to
`fun {T : Type}` and `BindingAllocatorInst.allocate` to
`BindingAllocatorInst.allocate (T := T)`. No generated computation is changed.

The five external standard-library operations have total constructive Lean definitions: generic
`Option<T>::clone` delegates to the supplied clone dictionary, `Result::err` pattern-matches the
result, String equality uses Lean's decidable String equality, String emptiness uses
`String.isEmpty`, and immutable String clone is identity. None is an axiom or opaque success.

The generated public function is transparent, and every generated finite loop used by the public
path has checked all-input termination and an exact accumulator/reference theorem. This covers
signature scans, argument-error scans, checked `usize` overflow and first-error precedence,
fixed-star and outer argument expansion records and evaluation order, type-mismatch scans, all
canonical-environment parameter classes, and residual positional/named capture. There is no
application-level argument cap: only source `usize` arithmetic bounds remain, and every fallible
allocation site has a stable typed `AllocationFailed { site, requested }` outcome.

`BindCallFull.Proofs.bind_call_with_allocator_matches_exact_reference` composes signature
validation, expansion, call validation, and canonical-environment construction through the
generated public entrypoint. The relation distinguishes malformed signatures, phase-specific count
overflow, every ordered allocation failure, expansion errors, call-validation errors, and
successful canonical environments. It is intentionally nondeterministic only where the external
allocator is nondeterministic. `bindingResultView_injective` proves that the final successful view
does not identify distinct generated environments. The release-facing axiom audit must contain no
`sorryAx` or project-owned axiom; allocator behavior is an explicit source-bound external contract,
not an always-success axiom.
