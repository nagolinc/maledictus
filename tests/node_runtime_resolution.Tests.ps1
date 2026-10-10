$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
. (Join-Path $repositoryRoot "scripts/resolve-node-runtime.ps1")
$actualNode = (Get-Command node -CommandType Application -ErrorAction Stop | Select-Object -First 1).Source
$caseRoot = Join-Path $repositoryRoot (".cache/node-runtime-tests/" + [guid]::NewGuid().ToString("N"))
$first = Join-Path $caseRoot "first"
$second = Join-Path $caseRoot "second"
New-Item -ItemType Directory -Path $first, $second -Force | Out-Null
Copy-Item -LiteralPath $actualNode -Destination (Join-Path $first "node.exe")
Copy-Item -LiteralPath $actualNode -Destination (Join-Path $second "node.exe")
$priorPath = $env:PATH
$priorOverride = Get-Item Env:MALEDICTUS_NODE -ErrorAction SilentlyContinue
try {
    $env:PATH = "$first;$second;$priorPath"
    Remove-Item Env:MALEDICTUS_NODE -ErrorAction SilentlyContinue
    if (@(Get-Command node -CommandType Application).Count -lt 2) {
        throw "fixture did not reproduce multiple Node installations on PATH"
    }
    $selected = Resolve-MaledictusNodeRuntime
    if ($selected -isnot [string] -or $selected -cne (Join-Path $first "node.exe")) {
        throw "PATH resolution did not select exactly the first Node executable: $selected"
    }
    $version = (& $selected --version | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or -not $version.StartsWith("v")) {
        throw "selected Node could not execute: $version"
    }
    if ((Get-FileHash -LiteralPath $selected).Hash -cne (Get-FileHash -LiteralPath $actualNode).Hash) {
        throw "selected runtime identity differs from the fixture executable"
    }
    $env:PATH = "$second;$first;$priorPath"
    if ((Resolve-MaledictusNodeRuntime) -cne (Join-Path $second "node.exe")) {
        throw "reversing PATH did not reverse the selected runtime"
    }
    $env:MALEDICTUS_NODE = Join-Path $second "node.exe"
    if ((Resolve-MaledictusNodeRuntime) -cne $env:MALEDICTUS_NODE) {
        throw "explicit runtime override was not honored"
    }
    $env:MALEDICTUS_NODE = Join-Path $caseRoot "missing.exe"
    $missingRejected = $false
    try { Resolve-MaledictusNodeRuntime | Out-Null }
    catch { $missingRejected = $true }
    if (-not $missingRejected) { throw "missing explicit runtime silently fell back to PATH" }
} finally {
    $env:PATH = $priorPath
    if ($null -eq $priorOverride) {
        Remove-Item Env:MALEDICTUS_NODE -ErrorAction SilentlyContinue
    } else {
        $env:MALEDICTUS_NODE = $priorOverride.Value
    }
}
Write-Output "Node runtime resolution passed multiple-PATH, reversed-PATH, execution/identity, explicit override and missing override controls."
