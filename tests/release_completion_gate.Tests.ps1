$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$testRoot = Join-Path $repositoryRoot ".cache/release-completion-gate-tests"
$caseRoot = Join-Path $testRoot ([guid]::NewGuid().ToString("N"))
New-Item -ItemType Directory -Path $caseRoot -Force | Out-Null

function Write-Json {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Path,
        [Parameter(Mandatory = $true)]
        [object]$Value
    )

    $json = $Value | ConvertTo-Json -Depth 20
    $utf8 = [System.Text.UTF8Encoding]::new($false)
    [System.IO.File]::WriteAllText($Path, $json + [Environment]::NewLine, $utf8)
}

function Invoke-EvidenceCheck {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Requirements,
        [Parameter(Mandatory = $true)]
        [string]$Classification,
        [Parameter(Mandatory = $true)]
        [string]$Coverage,
        [Parameter(Mandatory = $true)]
        [string]$Examples
    )

    $hostExecutable = (Get-Process -Id $PID).Path
    $priorErrorAction = $ErrorActionPreference
    $ErrorActionPreference = "Continue"
    try {
        $output = & $hostExecutable -NoProfile -NonInteractive -File `
            (Join-Path $repositoryRoot "scripts/assert-release-evidence.ps1") `
            -Requirements $Requirements `
            -ClassificationReport $Classification `
            -CoverageReport $Coverage `
            -ExamplesRoot $Examples 2>&1
        $exitCode = $LASTEXITCODE
    } finally {
        $ErrorActionPreference = $priorErrorAction
    }
    return [pscustomobject]@{
        ExitCode = $exitCode
        Output = ($output -join [Environment]::NewLine)
    }
}

try {
    $examples = Join-Path $caseRoot "examples"
    New-Item -ItemType Directory -Path $examples | Out-Null
    foreach ($name in @("one.request.json", "two.request.json")) {
        [System.IO.File]::WriteAllText((Join-Path $examples $name), "{}`n")
    }

    $requirements = [ordered]@{
        schema = "maledictus-release-completion/v1"
        classification = [ordered]@{
            report_schema = "maledictus-nagini-combined-classification/v4"
            suite_commit = "pinned-commit"
            roots = @("tests/functional")
            total = 3
            profile_ignored = 1
            evaluated = 2
            exact_match_kinds = @(
                "semantic-verification",
                "production-typecheck-rejection",
                "source-wellformedness-rejection"
            )
        }
        formal = [ordered]@{
            report_schema = "maledictus-formal-coverage/v2"
        }
        examples = [ordered]@{
            requests = @("one.request.json", "two.request.json")
        }
    }
    $classification = [ordered]@{
        schema = "maledictus-nagini-combined-classification/v4"
        suite_commit = "pinned-commit"
        roots = @("tests/functional")
        total = 3
        matched = 2
        semantic_matched = 1
        production_typecheck_rejection_matched = 1
        source_wellformedness_rejection_matched = 0
        profile_ignored = 1
        superseded_upstream_unsupported = 0
        production_typecheck_divergent = 0
        mismatched = 0
        refused = 0
        fixtures = @(
            [ordered]@{ fixture = "a.py"; status = "matched"; match_kind = "semantic-verification" },
            [ordered]@{ fixture = "b.py"; status = "matched"; match_kind = "production-typecheck-rejection" },
            [ordered]@{
                fixture = "ignored.py"
                status = "profile-ignored"
                match_kind = "profile-ignored"
                annotation_profile = [ordered]@{ ignored = $true }
            }
        )
    }
    $proof = [ordered]@{
        schema = "maledictus-formal-coverage/v2"
        root = [ordered]@{ composition_proved = $true }
        metrics = [ordered]@{
            source_unconditional_proved = 2
            source_conditional_proved = 0
            source_model_only = 0
            source_unproved = 0
            source_total = 2
            external_closed = 1
            external_total = 1
            root_composition_proved = $true
            whole_type_system_formally_proven = $true
        }
        source_nodes = @(
            [ordered]@{
                basis = "unconditional-source-bound"
                proof = [ordered]@{
                    current_source_hash_matches = $true
                    counts_as_implementation_refinement = $true
                    proof_obligations_closed = $true
                    axiom_audit_clean = $true
                }
            },
            [ordered]@{
                basis = "unconditional-source-bound"
                proof = [ordered]@{
                    current_source_hash_matches = $true
                    counts_as_implementation_refinement = $true
                    proof_obligations_closed = $true
                    axiom_audit_clean = $true
                }
            }
        )
        external_boundaries = @(
            [ordered]@{ contract = [ordered]@{ theorem = "closed" } }
        )
    }

    $requirementsPath = Join-Path $caseRoot "requirements.json"
    $classificationPath = Join-Path $caseRoot "classification.json"
    $coveragePath = Join-Path $caseRoot "coverage.json"
    Write-Json $requirementsPath $requirements
    Write-Json $classificationPath $classification
    Write-Json $coveragePath $proof

    $passing = Invoke-EvidenceCheck $requirementsPath $classificationPath $coveragePath $examples
    if ($passing.ExitCode -ne 0 -or $passing.Output -notlike "*release evidence is complete*") {
        throw "complete evidence did not pass: $($passing.Output)"
    }

    $classification.refused = 1
    $classification.matched = 1
    $classification.fixtures[1].status = "refused"
    $classification.fixtures[1].match_kind = $null
    Write-Json $classificationPath $classification
    $refused = Invoke-EvidenceCheck $requirementsPath $classificationPath $coveragePath $examples
    if ($refused.ExitCode -eq 0 -or $refused.Output -notlike "*exactly matched fixtures*") {
        throw "refused classification did not fail closed: $($refused.Output)"
    }

    $classification.refused = 0
    $classification.matched = 2
    $classification.fixtures[1].status = "matched"
    $classification.fixtures[1].match_kind = "production-typecheck-rejection"
    Write-Json $classificationPath $classification
    $proof.metrics.source_unconditional_proved = 1
    $proof.metrics.source_unproved = 1
    $proof.source_nodes[1].basis = "unproved"
    Write-Json $coveragePath $proof
    $partialProof = Invoke-EvidenceCheck $requirementsPath $classificationPath $coveragePath $examples
    if ($partialProof.ExitCode -eq 0 -or $partialProof.Output -notlike "*unconditional source proof coverage*") {
        throw "partial formal coverage did not fail closed: $($partialProof.Output)"
    }

    $proof.metrics.source_unconditional_proved = 2
    $proof.metrics.source_unproved = 0
    $proof.source_nodes[1].basis = "unconditional-source-bound"
    Write-Json $coveragePath $proof
    Remove-Item -LiteralPath (Join-Path $examples "two.request.json")
    $missingExample = Invoke-EvidenceCheck $requirementsPath $classificationPath $coveragePath $examples
    if ($missingExample.ExitCode -eq 0 -or $missingExample.Output -notlike "*checked-in example requests count*") {
        throw "missing example did not fail closed: $($missingExample.Output)"
    }

    [System.IO.File]::WriteAllText($coveragePath, "not json`n")
    $malformed = Invoke-EvidenceCheck $requirementsPath $classificationPath $coveragePath $examples
    if ($malformed.ExitCode -eq 0 -or $malformed.Output -notlike "*formal coverage report is not valid JSON*") {
        throw "malformed evidence did not fail closed: $($malformed.Output)"
    }

    Write-Output "release completion evidence passes only with exact classification, complete proofs, and the pinned example set"
} finally {
    if (Test-Path -LiteralPath $caseRoot) {
        Remove-Item -LiteralPath $caseRoot -Recurse -Force
    }
}
