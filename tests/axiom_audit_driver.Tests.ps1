$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$hostExecutable = (Get-Process -Id $PID).Path
$caseRoot = Join-Path $repositoryRoot (".cache/axiom-audit-driver-tests/" + [guid]::NewGuid().ToString("N"))
$formalRoot = Join-Path $caseRoot "formal"
$extractionRoot = Join-Path $formalRoot "extraction"
New-Item -ItemType Directory -Path $extractionRoot -Force | Out-Null
Copy-Item -LiteralPath (Join-Path $repositoryRoot "formal/extraction/test-axiom-audits.ps1") `
    -Destination (Join-Path $extractionRoot "test-axiom-audits.ps1")

$utf8 = [System.Text.UTF8Encoding]::new($false)
$runner = @'
param(
    [string] $Project,
    [string] $LakePath,
    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]] $LakeArguments
)
$fixtureRoot = Split-Path -Parent $PSScriptRoot
$mode = [System.IO.File]::ReadAllText((Join-Path $fixtureRoot "mode.txt")).Trim()
$positive = $LakeArguments[0] -eq "build"
$kind = if ($positive) { "positive" } else { "negative" }
$target = $LakeArguments[-1]
$event = [ordered]@{ kind = $kind; project = $Project; target = $target }
[System.IO.File]::AppendAllText(
    (Join-Path $fixtureRoot "calls.jsonl"),
    ($event | ConvertTo-Json -Compress) + [Environment]::NewLine
)
$lastProject = $Project -eq "solver-adjacent-order"
if ($positive) {
    if ($mode -eq "positive-failed" -and $lastProject) {
        & $LakePath -NoProfile -NonInteractive -Command "Write-Output 'positive compile failure control'; exit 1"
    } else {
        & $LakePath -NoProfile -NonInteractive -Command "Write-Output 'positive audit passed'; exit 0"
    }
} elseif ($mode -eq "negative-passed" -and $lastProject -and $target.EndsWith("AxiomAuditRejectsProjectAxiom.lean")) {
    & $LakePath -NoProfile -NonInteractive -Command "Write-Output 'negative unexpectedly accepted'; exit 0"
} elseif ($mode -eq "wrong-diagnostic" -and $lastProject -and $target.EndsWith("AxiomAuditRejectsProjectAxiom.lean")) {
    & $LakePath -NoProfile -NonInteractive -Command "Write-Output 'unrelated parser failure control'; exit 1"
} elseif ($target.EndsWith("AxiomAuditRejectsSorry.lean")) {
    & $LakePath -NoProfile -NonInteractive -Command "Write-Output 'axiom audit failed: got [sorryAx]'; exit 1"
} else {
    & $LakePath -NoProfile -NonInteractive -Command "Write-Output 'axiom audit failed: untrustedAssumption'; exit 1"
}
exit $LASTEXITCODE
'@
[System.IO.File]::WriteAllText((Join-Path $formalRoot "run-lake.ps1"), $runner, $utf8)

$hygiene = @'
param([string] $LakePath)
$fixtureRoot = Split-Path -Parent $PSScriptRoot
$event = [ordered]@{ kind = "hygiene"; project = ""; target = "" }
[System.IO.File]::AppendAllText(
    (Join-Path $fixtureRoot "calls.jsonl"),
    ($event | ConvertTo-Json -Compress) + [Environment]::NewLine
)
$mode = [System.IO.File]::ReadAllText((Join-Path $fixtureRoot "mode.txt")).Trim()
if ($mode -eq "hygiene-failed") {
    & $LakePath -NoProfile -NonInteractive -Command "Write-Output 'hygiene failure control'; exit 1"
} else {
    & $LakePath -NoProfile -NonInteractive -Command "exit 0"
}
exit $LASTEXITCODE
'@
[System.IO.File]::WriteAllText((Join-Path $formalRoot "test-lake-cache-hygiene.ps1"), $hygiene, $utf8)

# GitHub Actions prepends the stop preference and appends this native status
# forwarding to PowerShell steps. Exercise the actual copied root driver.
$wrapper = @'
$ErrorActionPreference = 'Stop'
& (Join-Path $PSScriptRoot "formal/extraction/test-axiom-audits.ps1") `
    -LakePath (Get-Process -Id $PID).Path
if ((Test-Path -LiteralPath variable:\LASTEXITCODE)) { exit $LASTEXITCODE }
'@
$wrapperPath = Join-Path $caseRoot "github-wrapper.ps1"
[System.IO.File]::WriteAllText($wrapperPath, $wrapper, $utf8)

function Invoke-DriverCase {
    param([string] $Mode)

    [System.IO.File]::WriteAllText((Join-Path $caseRoot "mode.txt"), $Mode, $utf8)
    [System.IO.File]::WriteAllText((Join-Path $caseRoot "calls.jsonl"), "", $utf8)
    $priorExit = Get-Variable LASTEXITCODE -Scope Global -ErrorAction SilentlyContinue
    $hadPriorExit = $null -ne $priorExit
    $priorExitCode = if ($hadPriorExit) { $priorExit.Value } else { $null }
    $priorErrorAction = $ErrorActionPreference
    $ErrorActionPreference = "Continue"
    try {
        $output = & $hostExecutable -NoProfile -NonInteractive -ExecutionPolicy Bypass `
            -File $wrapperPath 2>&1 | Out-String
        $exitCode = $LASTEXITCODE
    } finally {
        $ErrorActionPreference = $priorErrorAction
        if ($hadPriorExit) {
            $global:LASTEXITCODE = $priorExitCode
        } else {
            Remove-Variable LASTEXITCODE -Scope Global -ErrorAction SilentlyContinue
        }
    }
    [System.IO.File]::WriteAllText((Join-Path $caseRoot "$Mode.output.txt"), $output, $utf8)
    $calls = @([System.IO.File]::ReadAllLines((Join-Path $caseRoot "calls.jsonl")) |
        ForEach-Object { $_ | ConvertFrom-Json })
    return [pscustomobject]@{ ExitCode = $exitCode; Output = $output; Calls = $calls }
}

$passing = Invoke-DriverCase "pass"
if ($passing.ExitCode -ne 0 -or
    -not $passing.Output.Contains("All extraction axiom audits passed")) {
    throw "expected negative proofs poisoned the CI exit status ($($passing.ExitCode)); evidence: $caseRoot`n$($passing.Output)"
}
if (@($passing.Calls | Where-Object kind -eq "hygiene").Count -ne 1 -or
    @($passing.Calls | Where-Object kind -eq "positive").Count -ne 9 -or
    @($passing.Calls | Where-Object kind -eq "negative").Count -ne 18 -or
    @($passing.Calls | Where-Object kind -eq "positive" | Select-Object -ExpandProperty project -Unique).Count -ne 9) {
    throw "the actual root driver did not execute all nine projects and both negative fixtures"
}

$negativePassed = Invoke-DriverCase "negative-passed"
if ($negativePassed.ExitCode -ne 1 -or -not $negativePassed.Output.Contains("unexpectedly passed")) {
    throw "an unexpectedly passing negative proof was not fatal: $($negativePassed.Output)"
}
$wrongDiagnostic = Invoke-DriverCase "wrong-diagnostic"
if ($wrongDiagnostic.ExitCode -ne 1 -or -not $wrongDiagnostic.Output.Contains("failed for an unexpected reason")) {
    throw "an unrelated negative-fixture error was not fatal: $($wrongDiagnostic.Output)"
}
$positiveFailed = Invoke-DriverCase "positive-failed"
if ($positiveFailed.ExitCode -ne 1 -or -not $positiveFailed.Output.Contains("positive axiom audit failed")) {
    throw "a failed positive proof was not fatal: $($positiveFailed.Output)"
}
$hygieneFailed = Invoke-DriverCase "hygiene-failed"
if ($hygieneFailed.ExitCode -ne 1 -or -not $hygieneFailed.Output.Contains("Lake cache hygiene gate failed")) {
    throw "a failed cache hygiene check was not fatal: $($hygieneFailed.Output)"
}

Write-Output "Root axiom driver passed five behavioral controls under PowerShell $($PSVersionTable.PSVersion); retained evidence: $caseRoot"
