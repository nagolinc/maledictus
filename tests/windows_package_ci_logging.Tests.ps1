$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$hostExecutable = (Get-Process -Id $PID).Path
$caseRoot = Join-Path $repositoryRoot (".cache/windows-package-ci-tests/" + [guid]::NewGuid().ToString("N"))
$scriptsRoot = Join-Path $caseRoot "scripts"
New-Item -ItemType Directory -Path $scriptsRoot -Force | Out-Null
Copy-Item -LiteralPath (Join-Path $repositoryRoot "scripts/verify-windows-package-ci.ps1") -Destination $scriptsRoot
$utf8 = [System.Text.UTF8Encoding]::new($false)
$stub = @'
param([string] $Destination, [string] $NaginiSource)
switch ($Destination) {
    "pass" { Write-Output "verified payload and examples control"; exit 0 }
    "throw" { throw "exact failure control: mismatched payload digest" }
    "exit" { Write-Output "native exit control"; exit 23 }
    "fallthrough" {
        & (Get-Process -Id $PID).Path -NoProfile -NonInteractive -Command "exit 31"
        Write-Output "normal return after native failure control"
    }
    "redact" {
        Write-Output ("prefix " * 1000)
        Write-Output "Authorization: Bearer dummy-private-value"
        Write-Output 'password=synthetic-password token=synthetic-token secret="synthetic secret"'
        Write-Output 'https://dummy-user:dummy-password@example.invalid/path'
        Write-Output 'ghp_syntheticcredentialvalue'
        Write-Output "100% exact diagnostic`n::error title=injected::must remain message data"
        exit 17
    }
    default { throw "unknown test mode" }
}
'@
[System.IO.File]::WriteAllText((Join-Path $scriptsRoot "verify-windows-package.ps1"), $stub, $utf8)
$wrapperPath = Join-Path $caseRoot "github-wrapper.ps1"
$wrapper = @'
param([string] $Mode)
$ErrorActionPreference = 'Stop'
& (Join-Path $PSScriptRoot "scripts/verify-windows-package-ci.ps1") -Destination $Mode
if ((Test-Path -LiteralPath variable:\LASTEXITCODE)) { exit $LASTEXITCODE }
'@
[System.IO.File]::WriteAllText($wrapperPath, $wrapper, $utf8)

function Invoke-LoggingCase {
    param([string] $Mode)

    $priorExit = Get-Variable LASTEXITCODE -Scope Global -ErrorAction SilentlyContinue
    $hadExit = $null -ne $priorExit
    $priorCode = if ($hadExit) { $priorExit.Value } else { $null }
    $priorPreference = $ErrorActionPreference
    $ErrorActionPreference = "Continue"
    try {
        $output = & $hostExecutable -NoProfile -NonInteractive -ExecutionPolicy Bypass `
            -File $wrapperPath -Mode $Mode 2>&1 | Out-String
        $exitCode = $LASTEXITCODE
    } finally {
        $ErrorActionPreference = $priorPreference
        if ($hadExit) { $global:LASTEXITCODE = $priorCode }
        else { Remove-Variable LASTEXITCODE -Scope Global -ErrorAction SilentlyContinue }
    }
    $logPath = Join-Path $caseRoot ".cache/windows-package-verification.log"
    $log = [System.IO.File]::ReadAllText($logPath)
    [System.IO.File]::WriteAllText((Join-Path $caseRoot "$Mode.output.txt"), $output, $utf8)
    [System.IO.File]::WriteAllText((Join-Path $caseRoot "$Mode.log.txt"), $log, $utf8)
    return [pscustomobject]@{ ExitCode = $exitCode; Output = $output; Log = $log }
}

$success = Invoke-LoggingCase "pass"
if ($success.ExitCode -ne 0 -or -not $success.Log.Contains("verified payload and examples control") -or
    $success.Output.Contains("::error title=Windows package verification::")) {
    throw "successful verification was not preserved without an error annotation"
}
$thrown = Invoke-LoggingCase "throw"
if ($thrown.ExitCode -ne 1 -or -not $thrown.Log.Contains("exact failure control: mismatched payload digest") -or
    -not $thrown.Output.Contains("::error title=Windows package verification::")) {
    throw "terminating verification error lost its actual diagnostic or failed status: $($thrown.Output)"
}
$native = Invoke-LoggingCase "exit"
if ($native.ExitCode -ne 23 -or -not $native.Log.Contains("native exit control")) {
    throw "wrapper changed the verifier's explicit native exit code"
}
$fallthrough = Invoke-LoggingCase "fallthrough"
if ($fallthrough.ExitCode -ne 31 -or
    -not $fallthrough.Log.Contains("normal return after native failure control") -or
    -not $fallthrough.Output.Contains("Verifier exited 31.")) {
    throw "wrapper masked a failed native child when the verifier returned normally"
}
$redacted = Invoke-LoggingCase "redact"
if ($redacted.ExitCode -ne 17) { throw "redaction changed the verifier's failure status" }
foreach ($forbidden in @("dummy-private-value", "synthetic-password", "synthetic-token", "synthetic secret",
    "dummy-user:dummy-password", "ghp_syntheticcredentialvalue")) {
    if ($redacted.Output.Contains($forbidden) -or $redacted.Log.Contains($forbidden)) {
        throw "credential-shaped diagnostic data was not redacted"
    }
}
$annotations = @($redacted.Output -split "`r?`n" | Where-Object { $_.StartsWith("::error title=Windows package verification::") })
$commands = @($redacted.Output -split "`r?`n" | Where-Object { $_.StartsWith("::") })
if ($annotations.Count -ne 1 -or $commands.Count -ne 1 -or $annotations[0].Length -gt 2500 -or
    -not $annotations[0].Contains("100%25 exact diagnostic") -or
    -not $annotations[0].Contains("%0A::error title=injected::")) {
    throw "failure annotation was not bounded and escaped as one workflow command"
}
if (-not $redacted.Log.Contains("prefix prefix") -or -not $redacted.Log.Contains("[REDACTED]")) {
    throw "complete redacted stdout/stderr was not retained"
}
Write-Output "Windows CI logging passed five behavioral controls under PowerShell $($PSVersionTable.PSVersion); evidence: $caseRoot"
