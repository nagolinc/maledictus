param(
    [string] $Destination = ".cache/release/windows-x86_64",
    [string] $NaginiSource = ".upstream/nagini/src",
    [string] $LogPath = ".cache/windows-package-verification.log"
)

$ErrorActionPreference = "Stop"
$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$hostExecutable = (Get-Process -Id $PID).Path
$verifier = Join-Path $PSScriptRoot "verify-windows-package.ps1"
$logFullPath = [System.IO.Path]::GetFullPath((Join-Path $repositoryRoot $LogPath))
$cachePrefix = [System.IO.Path]::GetFullPath((Join-Path $repositoryRoot ".cache")) + [System.IO.Path]::DirectorySeparatorChar
if (-not $logFullPath.StartsWith($cachePrefix, [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "CI verification log must remain below the repository .cache directory"
}
New-Item -ItemType Directory -Path (Split-Path -Parent $logFullPath) -Force | Out-Null
$childWrapperPath = Join-Path (Split-Path -Parent $logFullPath) "windows-package-verification-child.ps1"
$childWrapper = @'
param([string] $Verifier, [string] $Destination, [string] $NaginiSource)
$ErrorActionPreference = 'Stop'
& $Verifier -Destination $Destination -NaginiSource $NaginiSource
if ((Test-Path -LiteralPath variable:\LASTEXITCODE)) { exit $LASTEXITCODE }
'@
[System.IO.File]::WriteAllText($childWrapperPath, $childWrapper, [System.Text.UTF8Encoding]::new($false))

function ConvertTo-SafeDiagnostic {
    param([string] $Text)

    $safe = $Text.Replace($repositoryRoot, "<workspace>").Replace($repositoryRoot.Replace("\", "/"), "<workspace>")
    $safe = [regex]::Replace($safe, '\x1b\[[0-?]*[ -/]*[@-~]', '')
    # Redact credential-shaped text in diagnostics; never enumerate environment
    # variables, inspect credentials, or put their values into the log.
    $safe = [regex]::Replace($safe, '(?im)(\b(?:proxy-authorization|authorization)\s*:\s*)[^\r\n]+', '$1[REDACTED]')
    $safe = [regex]::Replace($safe, '(?i)(\b(?:access_token|token|password|secret)\s*[=:]\s*)(?:"[^"]*"|''[^'']*''|[^\s&]+)', '$1[REDACTED]')
    $safe = [regex]::Replace($safe, '(?i)(https?://)[^/\s@]+@', '$1[REDACTED]@')
    return [regex]::Replace($safe, '\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+)\b', '[REDACTED]')
}

$exitCode = 1
$output = ""
$priorErrorAction = $ErrorActionPreference
$ErrorActionPreference = "Continue"
try {
    # Keep GitHub's appended native-exit forwarding even when the actual script
    # returns normally after a failing native child. Plain -File would mask it.
    $output = & $hostExecutable -NoProfile -NonInteractive -ExecutionPolicy Bypass `
        -File $childWrapperPath -Verifier $verifier -Destination $Destination `
        -NaginiSource $NaginiSource 2>&1 | Out-String
    $exitCode = $LASTEXITCODE
} catch {
    $output = $_ | Out-String
} finally {
    $ErrorActionPreference = $priorErrorAction
}

$safeOutput = ConvertTo-SafeDiagnostic $output
[System.IO.File]::WriteAllText(
    $logFullPath,
    "Verifier process exit: $exitCode`n$safeOutput",
    [System.Text.UTF8Encoding]::new($false)
)
# Do not replay arbitrary diagnostic lines as live workflow commands. Full
# redacted output is in the artifact; the public failure annotation is escaped.
Write-Output "Windows package verifier process exit: $exitCode; log: $LogPath"

if ($exitCode -ne 0) {
    # Keep the public check annotation bounded; the complete redacted output is
    # retained as an artifact. Escape workflow syntax, including injected lines.
    $summaryLimit = 2048
    $summary = $safeOutput.Trim()
    if ($summary.Length -gt $summaryLimit) {
        $summary = "[earlier output retained in artifact] " + $summary.Substring($summary.Length - $summaryLimit)
    }
    if ([string]::IsNullOrWhiteSpace($summary)) {
        $summary = "The verifier produced no diagnostic output."
    }
    $summary = $summary.Replace("%", "%25").Replace("`r", "%0D").Replace("`n", "%0A")
    Write-Output "::error title=Windows package verification::Verifier exited $exitCode. $summary"
}
exit $exitCode
