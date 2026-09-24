param(
    [Parameter(Mandatory = $true)]
    [string] $LakePath
)

$ErrorActionPreference = "Stop"
if (Test-Path -LiteralPath $LakePath) {
    $LakePath = (Resolve-Path -LiteralPath $LakePath).Path
}
else {
    $lakeCommand = Get-Command -Name $LakePath -CommandType Application -ErrorAction Stop
    $LakePath = $lakeCommand.Source
}
$workspace = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$runner = Join-Path $workspace "formal/run-lake.ps1"

& (Join-Path $workspace "formal/test-lake-cache-hygiene.ps1") -LakePath $LakePath
if ($LASTEXITCODE -ne 0) {
    throw "Lake cache hygiene gate failed"
}

$projects = @(
    @{
        Project = "obligation-kernel"
        Target = "ObligationKernelProofs.AxiomAudit"
    },
    @{
        Project = "call-binding-full"
        Target = "BindCallFullProofs.AxiomAudit"
    },
    @{
        Project = "vc-term-sort"
        Target = "VcTermSortProofs.AxiomAudit"
    },
    @{
        Project = "io-sort-kernel"
        Target = "IoSortKernelProofs.AxiomAudit"
    },
    @{
        Project = "persistent-collections"
        Target = "PersistentCollectionsProofs.AxiomAudit"
    },
    @{
        Project = "type-algebra-kernel"
        Target = "TypeAlgebraKernelProofs.AxiomAudit"
    },
    @{
        Project = "kernel-exit-effects"
        Target = "KernelExitEffectsProofs.AxiomAudit"
    },
    @{
        Project = "solver-sort-predicates"
        Target = "SolverSortPredicatesProofs.AxiomAudit"
    },
    @{
        Project = "solver-adjacent-order"
        Target = "SolverAdjacentOrderProofs.AxiomAudit"
    }
)

foreach ($project in $projects) {
    $buildOutput = & $runner `
        -Project $project.Project `
        -LakePath $LakePath `
        build $project.Target 2>&1 | Out-String
    if ($LASTEXITCODE -ne 0) {
        throw "positive axiom audit failed for $($project.Target):`n$buildOutput"
    }

    $negativeCases = @(
        @{
            Path = "tests/AxiomAuditRejectsSorry.lean"
            Expected = "got [sorryAx]"
        },
        @{
            Path = "tests/AxiomAuditRejectsProjectAxiom.lean"
            Expected = "untrustedAssumption"
        }
    )
    foreach ($negativeCase in $negativeCases) {
        $negativeOutput = & $runner `
            -Project $project.Project `
            -LakePath $LakePath `
            env lean $negativeCase.Path 2>&1 | Out-String
        if ($LASTEXITCODE -eq 0) {
            throw "negative axiom-audit fixture $($negativeCase.Path) unexpectedly passed for $($project.Target)"
        }
        if (!$negativeOutput.Contains($negativeCase.Expected)) {
            throw "negative axiom-audit fixture $($negativeCase.Path) failed for an unexpected reason:`n$negativeOutput"
        }
    }
}

Write-Output "All extraction axiom audits passed, and each rejected sorryAx and project-owned axiom dependencies."
