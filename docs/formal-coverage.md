# Formal implementation coverage

Maledictus does not infer whole-system formal correctness from the number of Lean theorems, test
fixtures, lines of code, or a passing proof for one helper. The checked artifact
[`formal/coverage.json`](../formal/coverage.json) defines a finite denominator tied to the current
production Rust source.

## Denominator

The root is the production issuance call `verify_internal(request, issuance = true)`. The generator
parses every Rust file below `src/`, excludes `#[cfg(test)]` bodies, and constructs an
over-approximating call graph by function and method name. Nested closures and local helper
functions are included in the source span and behavior of their containing function body.

Rust dispatch cannot always be resolved from syntax alone. A reachable macro expansion,
function-pointer call, callable field, method or trait dispatch, or unresolved callable name
activates the fail-closed fallback: every non-test source function enters the denominator. The
artifact records whether this happened and which source nodes caused it. Thus ambiguity can make
the denominator larger, never smaller. This is a syntactic `syn` analysis, not a MIR-derived call
graph.

Each source node has a stable identity derived from its qualified symbol, file, line span, and
source hash. A source-tree hash makes any Rust source change stale the checked artifact. Changes to
the generator, configuration, extraction manifests, proof artifacts, direct Cargo dependencies,
or abstract Lean models are also checked during regeneration.

## Numerators and claim rule

Every source node has exactly one basis:

- `unconditional-source-bound`: a current all-input source-correspondence theorem closes normal,
  error, and divergence behavior without an application premise.
- `conditional-source-bound`: the theorem has a stated premise that is not proved for the concrete
  production boundary.
- `model-only`: an abstract formal model without current Rust correspondence. Source nodes do not
  receive this classification merely because a related model exists.
- `unproved`: no qualifying source-bound theorem.

Abstract `formal/Maledictus/*.lean` modules are inventoried separately as `model-only` and always
contribute zero to the source numerator.

External semantic dependencies are a second finite denominator. The configuration explicitly
lists the SMT solver, parsers, strict typechecker process, TypeScript frontend, serialization,
hashing, operating-system services, and binder allocator. Every direct Cargo dependency must be
assigned to one of these boundaries or generation fails.

The artifact reports three independent results:

1. unconditional source-function coverage;
2. formally closed external-boundary coverage;
3. whether a theorem composes the real production root to the type-system specification.

`type system correctness formally proven` is true only when both coverage ratios are 100% and the
root composition theorem exists. Conditional proofs and abstract models remain visible but cannot
make that claim true.

## Reproduction

Use the repository-local Rust toolchain and keep build output under `.cache/`:

```powershell
$env:RUSTUP_HOME = (Resolve-Path .toolchains/rustup).Path
$env:CARGO_HOME = (Resolve-Path .toolchains/cargo).Path
$env:CARGO_TARGET_DIR = (Resolve-Path .cache).Path + '/formal-coverage-tool-target'

.\.toolchains\cargo\bin\cargo.exe run --offline `
  --manifest-path formal/coverage-tool/Cargo.toml -- `
  generate --project . --config formal/coverage-config.json --output formal/coverage.json
```

CI and audits should use the same command with `check` instead of `generate`. `check` regenerates
the complete artifact in memory and fails if any byte differs:

```powershell
.\.toolchains\cargo\bin\cargo.exe run --offline `
  --manifest-path formal/coverage-tool/Cargo.toml -- `
  check --project . --config formal/coverage-config.json --output formal/coverage.json
```

Focused generator behavior tests run with:

```powershell
.\.toolchains\cargo\bin\cargo.exe test --offline `
  --manifest-path formal/coverage-tool/Cargo.toml
```
