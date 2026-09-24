# Release-completion gate

[`conformance/release-completion-v1.json`](../conformance/release-completion-v1.json) pins the
complete release obligation. On Windows, run:

```powershell
./scripts/release-completion-gate.ps1
```

The command packages and independently verifies the release executable, proves every pinned
example through the packaged runtime, classifies all 620 Nagini fixtures, freshness-checks the
formal coverage ledger, and then fails unless all 607 evaluated fixtures match exactly, precisely
13 are profile-ignored, source and external proof coverage are both 100%, and the production root
composition and whole-system proof flags are true. Disposable evidence remains below `.cache/`.

The evidence parser's fail-closed behavior is exercised by:

```powershell
./tests/release_completion_gate.Tests.ps1
```

## Fast complete test suite

The repository contains many separate integration-test binaries. Standard `cargo test
--all-targets` executes those binaries serially and remains valid, but is unnecessarily slow for a
complete local or CI run. Install the pinned `cargo-nextest` 0.9.145 release and run:

```powershell
cargo nextest run --all-targets --no-fail-fast
cargo test --doc
```

Nextest changes only test scheduling: it runs the same Rust test inventory concurrently across
binaries. CI installs the same pinned release before executing this command.
