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
