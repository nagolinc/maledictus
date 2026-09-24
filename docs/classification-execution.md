# Authoritative classifier execution

`conformance classify-suite` evaluates every pinned fixture independently in the scalar, heap,
and reference lanes. The final JSON report remains the only machine-readable result on standard
output. Progress is written to standard error before each fixture starts, followed by a completion
event for each root/lane pair and the whole suite. This exposes both the current fixture and the
exact completed position without changing classification order or results.

The command reuses only fully validated per-fixture, per-lane results below
`.cache/classify-suite/`. A cache keyed only by fixture contents would be unsound: a result can
also depend on imported source files, the Maledictus implementation, fragment identities, pinned
typechecker and stub identities, and the upstream suite commit. Every one of those applicable
inputs is therefore part of the cache entry identity.

## Resumable execution

Each immutable cache entry binds all of:

- cache schema and classification lane;
- normalized fixture path and content digest;
- the exact pin-file digest, pinned suite commit, and an ordered digest of every pinned fixture
  root and fixture path;
- a canonical path-and-content digest over every `.py` and `.pyi` file in the suite, excluding
  `.git` internals. This intentionally over-binds the exact transitive import graph: every source
  that any fixture can load, as well as every source that could newly shadow a prior provider, is
  covered. A source change invalidates more entries than a minimal graph key would, but cannot
  leave a stale provider result valid;
- the running Maledictus executable digest and the sorted advertised Python fragment identities;
- the solver name, version, Rust binding identity, and verification-condition IR identity used by
  classification;
- the full production `PythonTypecheckerIdentity` when that lane invokes strict mypy. Lookup
  reprobes the current toolchain and compares the package, runtime, configuration, and contract
  support digests before accepting the entry;
- checked-external adapter, external-stub, and generated-interface identities. The current Nagini
  classifier API accepts none of these, so the v1 key requires all three collections to be empty.
  Adding such inputs requires a new implementation/schema that records their exact digests; an
  older entry cannot survive the executable digest change.

Classification reads from a source snapshot copied below the same cache root at run start. The
snapshot contains the bytes used to calculate the source-tree identity, so changes to the upstream
working tree during a long run cannot mix two source states into one cached result. The ordered
pinned-root inventory is also calculated from that same immutable snapshot. Python source symlinks
are refused instead of being followed outside the pinned tree.

Writes should use a temporary file in the same `.cache` directory followed by an atomic rename.
The implementation does so and prefixes each published filename with the canonical payload digest. A
temporary or malformed JSON file, unknown field/schema, wrong filename digest, mismatched key or
fixture, noncanonical result, stale typechecker identity, symlinked entry, or conflicting pair of
otherwise valid results is a cache miss. Such files are never classification results. Fresh work
is rerun in canonical fixture order and published under a new immutable filename, so a corrupt
old candidate cannot block recovery and an interrupted temporary file cannot be mistaken for a
completed entry.

Cached and fresh classifications both pass through the same lane counters, count reconciliation,
root/commit checks, canonical fixture sorting, and combined-report validation. The final JSON is
therefore byte-for-byte governed by the existing deterministic report structures rather than by
cache traversal order. Cache diagnostics never appear on standard output.

Before creating any directory, the runner resolves the repository root and `.cache`, rejects a
cache root outside that resolved tree, and rechecks every per-entry directory after creation. No
classifier cache or source snapshot is written outside the repository's `.cache` tree.

## Trust boundary

This is a non-adversarial local build cache. The payload digest detects incomplete writes,
accidental corruption, and stale or internally inconsistent entries; it is not a signature or an
authentication mechanism. A user or process that can rewrite an entry can also recompute its
digest. If the local cache's integrity is not trusted, delete `.cache/classify-suite` and rerun the
classifier from the pinned inputs.

Cached conformance classifications are only a performance and resumability optimization for
`conformance classify-suite`. They are not proof artifacts or certificate evidence. Certificate
issuance does not read `.cache/classify-suite` or call the cache-enabled classification entry
point; it performs its own verification from source-bound inputs.

## Windows binary launcher

Run long Windows classifications through `scripts/classify-suite.ps1`, passing the already-built
Maledictus executable, suite, and pin. The launcher hashes the executable bytes and publishes an
immutable runnable snapshot at `.cache/classifier-bin/<executable-sha256>/`. The snapshot contains
that exact executable, the selected `libz3.dll`, and a manifest binding both file digests. The
original Cargo target is closed before the snapshot process starts, so the classifier can keep
running while Cargo replaces `.cache/root-test-target/debug/maledictus.exe` during another build.

Publication copies into a uniquely named staging directory, verifies every copied digest, and then
atomically renames the complete directory. Concurrent launchers either publish the same complete
snapshot or validate and reuse the winner; they never execute a staging directory. An existing
snapshot with mismatched executable, Z3, or manifest bytes fails closed. Both staging and published
snapshots remain below the repository's `.cache` tree.

The copied executable still uses the resumable per-fixture cache at `.cache/classify-suite`; moving
the executable does not create a second result cache. Since executable bytes are unchanged, the
classifier cache's executable identity is also unchanged.

From the repository root, the standard development invocation is:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/classify-suite.ps1 `
    -Executable .cache/root-test-target/debug/maledictus.exe `
    -LibZ3 z3-5.1.0/bin/libz3.dll `
    -Suite .upstream/nagini `
    -Pin conformance/nagini-v1.3.1.json
```

`-LibZ3` may be omitted when the DLL is beside the source executable, in the current directory, or
on `PATH`. Passing it explicitly makes the selected native dependency unambiguous.
