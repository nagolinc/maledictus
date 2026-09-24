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
    $output = & $runner -Project solver-sort-predicates -LakePath $LakePath `
        env lean $negativeCase.Path 2>&1 | Out-String
    if ($LASTEXITCODE -eq 0 -or !$output.Contains($negativeCase.Expected)) {
        throw "negative solver-sort predicate audit failed unexpectedly:`n$output"
    }
}

Write-Output "Solver-sort predicate positive audit passed; both malicious negatives were rejected."
