param(
    [Parameter(Mandatory = $true)]
    [string] $LakePath
)

$ErrorActionPreference = "Stop"
$workspace = Split-Path -Parent (Split-Path -Parent (Split-Path -Parent $PSScriptRoot))
$runner = Join-Path $workspace "formal/run-lake.ps1"

$positive = & $runner -Project solver-sort-predicates -LakePath $LakePath `
    build SolverSortPredicatesProofs.AxiomAudit 2>&1 | Out-String
if ($LASTEXITCODE -ne 0) {
    throw "positive solver-sort predicate axiom audit failed:`n$positive"
}

$negativeCases = @(
    @{ Path = "tests/AxiomAuditRejectsSorry.lean"; Expected = "got [sorryAx]" },
    @{ Path = "tests/AxiomAuditRejectsProjectAxiom.lean"; Expected = "untrustedAssumption" }
)
foreach ($negativeCase in $negativeCases) {
    $priorNativeExit = Get-Variable LASTEXITCODE -Scope Global -ErrorAction SilentlyContinue
    $hadNativeExit = $null -ne $priorNativeExit
    $priorNativeExitCode = if ($hadNativeExit) { $priorNativeExit.Value } else { $null }
    try {
        $output = & $runner -Project solver-sort-predicates -LakePath $LakePath `
            env lean $negativeCase.Path 2>&1 | Out-String
        $negativeExitCode = $LASTEXITCODE
    } finally {
        # An expected proof rejection is test data, not the enclosing CI status.
        # A failed assertion below still throws; only the checked child status is restored.
        if ($hadNativeExit) {
            $global:LASTEXITCODE = $priorNativeExitCode
        } else {
            Remove-Variable LASTEXITCODE -Scope Global -ErrorAction SilentlyContinue
        }
    }
    if ($negativeExitCode -eq 0 -or !$output.Contains($negativeCase.Expected)) {
        throw "negative solver-sort predicate audit failed unexpectedly:`n$output"
    }
}

Write-Output "Solver-sort predicate positive audit passed; both malicious negatives were rejected."
