[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [string]$Requirements,

    [Parameter(Mandatory = $true)]
    [string]$ClassificationReport,

    [Parameter(Mandatory = $true)]
    [string]$CoverageReport,

    [Parameter(Mandatory = $true)]
    [string]$ExamplesRoot
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Read-JsonObject {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Path,
        [Parameter(Mandatory = $true)]
        [string]$Description
    )

    $resolved = (Resolve-Path -LiteralPath $Path -ErrorAction Stop).Path
    $item = Get-Item -LiteralPath $resolved -Force
    if ($item.PSIsContainer -or ($item.Attributes -band [System.IO.FileAttributes]::ReparsePoint)) {
        throw "$Description must be a regular file: $resolved"
    }
    try {
        return Get-Content -LiteralPath $resolved -Raw | ConvertFrom-Json -ErrorAction Stop
    } catch {
        throw "$Description is not valid JSON: $($_.Exception.Message)"
    }
}

function Get-RequiredProperty {
    param(
        [Parameter(Mandatory = $true)]
        [object]$Object,
        [Parameter(Mandatory = $true)]
        [string]$Name,
        [Parameter(Mandatory = $true)]
        [string]$Description
    )

    $property = $Object.PSObject.Properties[$Name]
    if ($null -eq $property) {
        throw "$Description omits required property '$Name'"
    }
    return $property.Value
}

function Assert-Equal {
    param(
        [Parameter(Mandatory = $true)]
        [AllowNull()]
        [object]$Actual,
        [Parameter(Mandatory = $true)]
        [AllowNull()]
        [object]$Expected,
        [Parameter(Mandatory = $true)]
        [string]$Description
    )

    if ($Actual -cne $Expected) {
        throw "${Description}: expected '$Expected', found '$Actual'"
    }
}

function Assert-ExactStringSequence {
    param(
        [Parameter(Mandatory = $true)]
        [AllowEmptyCollection()]
        [object[]]$Actual,
        [Parameter(Mandatory = $true)]
        [AllowEmptyCollection()]
        [object[]]$Expected,
        [Parameter(Mandatory = $true)]
        [string]$Description
    )

    if ($Actual.Count -ne $Expected.Count) {
        throw "$Description count: expected $($Expected.Count), found $($Actual.Count)"
    }
    for ($index = 0; $index -lt $Expected.Count; $index += 1) {
        Assert-Equal ([string]$Actual[$index]) ([string]$Expected[$index]) "$Description at index $index"
    }
}

$requirementsObject = Read-JsonObject $Requirements "release requirements"
Assert-Equal `
    (Get-RequiredProperty $requirementsObject "schema" "release requirements") `
    "maledictus-release-completion/v1" `
    "release requirements schema"

$classificationRequirements = Get-RequiredProperty `
    $requirementsObject "classification" "release requirements"
$formalRequirements = Get-RequiredProperty $requirementsObject "formal" "release requirements"
$exampleRequirements = Get-RequiredProperty $requirementsObject "examples" "release requirements"

$classification = Read-JsonObject $ClassificationReport "classification report"
Assert-Equal `
    (Get-RequiredProperty $classification "schema" "classification report") `
    (Get-RequiredProperty $classificationRequirements "report_schema" "classification requirements") `
    "classification report schema"
Assert-Equal `
    (Get-RequiredProperty $classification "suite_commit" "classification report") `
    (Get-RequiredProperty $classificationRequirements "suite_commit" "classification requirements") `
    "classification suite commit"
Assert-ExactStringSequence `
    @(Get-RequiredProperty $classification "roots" "classification report") `
    @(Get-RequiredProperty $classificationRequirements "roots" "classification requirements") `
    "classification roots"

$total = [int64](Get-RequiredProperty $classificationRequirements "total" "classification requirements")
$ignored = [int64](Get-RequiredProperty $classificationRequirements "profile_ignored" "classification requirements")
$evaluated = [int64](Get-RequiredProperty $classificationRequirements "evaluated" "classification requirements")
if ($ignored + $evaluated -ne $total) {
    throw "release requirements do not reconcile: ignored + evaluated must equal total"
}
Assert-Equal ([int64](Get-RequiredProperty $classification "total" "classification report")) $total "classification total"
Assert-Equal ([int64](Get-RequiredProperty $classification "profile_ignored" "classification report")) $ignored "profile-ignored fixtures"
Assert-Equal ([int64](Get-RequiredProperty $classification "matched" "classification report")) $evaluated "exactly matched fixtures"

foreach ($field in @(
    "superseded_upstream_unsupported",
    "production_typecheck_divergent",
    "mismatched",
    "refused"
)) {
    Assert-Equal `
        ([int64](Get-RequiredProperty $classification $field "classification report")) `
        ([int64]0) `
        "classification $field"
}

$fixtures = @(Get-RequiredProperty $classification "fixtures" "classification report")
Assert-Equal ([int64]$fixtures.Count) $total "classification fixture records"
$fixtureNames = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
$matchedFixtures = 0
$ignoredFixtures = 0
$allowedKinds = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
$matchKindCounts = @{}
foreach ($kind in @(Get-RequiredProperty $classificationRequirements "exact_match_kinds" "classification requirements")) {
    if (-not $allowedKinds.Add([string]$kind)) {
        throw "classification requirements contain duplicate exact match kind '$kind'"
    }
    $matchKindCounts[[string]$kind] = 0
}
foreach ($fixture in $fixtures) {
    $fixtureName = [string](Get-RequiredProperty $fixture "fixture" "classification fixture")
    if ([string]::IsNullOrWhiteSpace($fixtureName) -or -not $fixtureNames.Add($fixtureName)) {
        throw "classification report contains an empty or duplicate fixture '$fixtureName'"
    }
    $status = [string](Get-RequiredProperty $fixture "status" "classification fixture $fixtureName")
    $matchKind = [string](Get-RequiredProperty $fixture "match_kind" "classification fixture $fixtureName")
    if ($status -ceq "matched" -and $allowedKinds.Contains($matchKind)) {
        $matchedFixtures += 1
        $matchKindCounts[$matchKind] += 1
    } elseif ($status -ceq "profile-ignored" -and $matchKind -ceq "profile-ignored") {
        $annotationProfile = Get-RequiredProperty `
            $fixture "annotation_profile" "profile-ignored fixture $fixtureName"
        Assert-Equal `
            (Get-RequiredProperty $annotationProfile "ignored" "profile-ignored fixture $fixtureName") `
            $true `
            "active profile annotation for $fixtureName"
        $ignoredFixtures += 1
    } else {
        throw "classification fixture $fixtureName is not an exact match or profile-ignored: status=$status, match_kind=$matchKind"
    }
}
Assert-Equal ([int64]$matchedFixtures) $evaluated "matched fixture records"
Assert-Equal ([int64]$ignoredFixtures) $ignored "profile-ignored fixture records"
foreach ($summary in @(
    @("semantic-verification", "semantic_matched"),
    @("production-typecheck-rejection", "production_typecheck_rejection_matched"),
    @("source-wellformedness-rejection", "source_wellformedness_rejection_matched")
)) {
    $kind = [string]$summary[0]
    $field = [string]$summary[1]
    Assert-Equal `
        ([int64](Get-RequiredProperty $classification $field "classification report")) `
        ([int64]$matchKindCounts[$kind]) `
        "classification $field"
}

$coverage = Read-JsonObject $CoverageReport "formal coverage report"
Assert-Equal `
    (Get-RequiredProperty $coverage "schema" "formal coverage report") `
    (Get-RequiredProperty $formalRequirements "report_schema" "formal requirements") `
    "formal coverage report schema"
$metrics = Get-RequiredProperty $coverage "metrics" "formal coverage report"
$sourceTotal = [int64](Get-RequiredProperty $metrics "source_total" "formal coverage metrics")
$sourceUnconditional = [int64](Get-RequiredProperty $metrics "source_unconditional_proved" "formal coverage metrics")
if ($sourceTotal -le 0) {
    throw "formal coverage source denominator must be positive"
}
Assert-Equal $sourceUnconditional $sourceTotal "unconditional source proof coverage"
foreach ($field in @("source_conditional_proved", "source_model_only", "source_unproved")) {
    Assert-Equal `
        ([int64](Get-RequiredProperty $metrics $field "formal coverage metrics")) `
        ([int64]0) `
        "formal coverage $field"
}
$externalTotal = [int64](Get-RequiredProperty $metrics "external_total" "formal coverage metrics")
$externalClosed = [int64](Get-RequiredProperty $metrics "external_closed" "formal coverage metrics")
if ($externalTotal -le 0) {
    throw "formal coverage external-boundary denominator must be positive"
}
Assert-Equal $externalClosed $externalTotal "closed external-boundary coverage"
Assert-Equal `
    (Get-RequiredProperty $metrics "root_composition_proved" "formal coverage metrics") `
    $true `
    "formal root composition"
Assert-Equal `
    (Get-RequiredProperty $metrics "whole_type_system_formally_proven" "formal coverage metrics") `
    $true `
    "whole-system formal proof"
$root = Get-RequiredProperty $coverage "root" "formal coverage report"
Assert-Equal `
    (Get-RequiredProperty $root "composition_proved" "formal coverage root") `
    $true `
    "formal root composition artifact"
$sourceNodes = @(Get-RequiredProperty $coverage "source_nodes" "formal coverage report")
Assert-Equal ([int64]$sourceNodes.Count) $sourceTotal "formal source-node records"
foreach ($node in $sourceNodes) {
    Assert-Equal `
        (Get-RequiredProperty $node "basis" "formal source node") `
        "unconditional-source-bound" `
        "formal source-node basis"
    $nodeProof = Get-RequiredProperty $node "proof" "formal source node"
    if ($null -eq $nodeProof) {
        throw "unconditional formal source node has no proof record"
    }
    foreach ($field in @(
        "current_source_hash_matches",
        "counts_as_implementation_refinement",
        "proof_obligations_closed",
        "axiom_audit_clean"
    )) {
        Assert-Equal `
            (Get-RequiredProperty $nodeProof $field "formal source-node proof") `
            $true `
            "formal source-node proof $field"
    }
}
$externalBoundaries = @(Get-RequiredProperty $coverage "external_boundaries" "formal coverage report")
Assert-Equal ([int64]$externalBoundaries.Count) $externalTotal "formal external-boundary records"
foreach ($boundary in $externalBoundaries) {
    if ($null -eq (Get-RequiredProperty $boundary "contract" "formal external boundary")) {
        throw "formal external boundary has no closed contract"
    }
}

$examplesPath = (Resolve-Path -LiteralPath $ExamplesRoot -ErrorAction Stop).Path
$exampleItem = Get-Item -LiteralPath $examplesPath -Force
if (-not $exampleItem.PSIsContainer -or
    ($exampleItem.Attributes -band [System.IO.FileAttributes]::ReparsePoint)) {
    throw "example root must be a regular directory: $examplesPath"
}
$actualExamples = @(
    Get-ChildItem -LiteralPath $examplesPath -File -Filter "*.request.json" |
        ForEach-Object { $_.Name } |
        Sort-Object -CaseSensitive
)
$expectedExamples = @(
    @(Get-RequiredProperty $exampleRequirements "requests" "example requirements") |
        ForEach-Object { [string]$_ } |
        Sort-Object -CaseSensitive
)
Assert-ExactStringSequence $actualExamples $expectedExamples "checked-in example requests"

Write-Output (
    "release evidence is complete: {0}/{1} evaluated fixtures match, {2} are profile-ignored, " +
    "{3}/{3} source functions and {4}/{4} external boundaries are formally closed, and {5} examples are pinned" -f
        $evaluated,
        $evaluated,
        $ignored,
        $sourceTotal,
        $externalTotal,
        $expectedExamples.Count
)
