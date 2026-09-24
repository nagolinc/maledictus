$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

function Assert-True {
    param(
        [Parameter(Mandatory = $true)][bool]$Condition,
        [Parameter(Mandatory = $true)][string]$Message
    )

    if (-not $Condition) {
        throw "Assertion failed: $Message"
    }
}

function Assert-Throws {
    param(
        [Parameter(Mandatory = $true)][scriptblock]$Action,
        [Parameter(Mandatory = $true)][string]$ExpectedMessage,
        [Parameter(Mandatory = $true)][string]$Message
    )

    $observedMessage = $null
    try {
        & $Action
    } catch {
        $observedMessage = $_.Exception.Message
    }
    Assert-True ($null -ne $observedMessage) $Message
    Assert-True (
        $observedMessage.IndexOf($ExpectedMessage, [StringComparison]::OrdinalIgnoreCase) -ge 0
    ) "$Message (unexpected diagnostic: $observedMessage)"
}

$testRoot = Join-Path ([IO.Path]::GetTempPath()) (
    "maledictus-vc-term-sort-setup-" + [Guid]::NewGuid().ToString("N")
)
$setupScript = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot "..\setup-extraction-workspace.ps1"))

try {
    $repository = Join-Path $testRoot "repository"
    $sourceDirectory = Join-Path $repository "src"
    $cache = Join-Path $repository ".cache"
    [IO.Directory]::CreateDirectory($sourceDirectory) | Out-Null
    $source = Join-Path $sourceDirectory "vc.rs"
    Set-Content -LiteralPath $source -Value "pub fn source_bound() {}" -NoNewline

    $workspace = Join-Path $cache "fresh"
    & $setupScript -RepositoryRoot $repository -WorkspacePath $workspace | Out-Null
    Assert-True (Test-Path -LiteralPath $cache -PathType Container) `
        "fresh setup creates a missing repository cache"
    $linkedSource = Join-Path $workspace "src\lib.rs"
    $linkedItem = Get-Item -LiteralPath $linkedSource -Force
    Assert-True ($linkedItem.LinkType -eq "HardLink") "fresh setup creates a hard link"
    Assert-True (
        @($linkedItem.Target).Count -eq 1 -and
        [IO.Path]::GetFullPath([string]$linkedItem.Target[0]).Equals(
            [IO.Path]::GetFullPath($source),
            [StringComparison]::OrdinalIgnoreCase
        )
    ) "fresh setup links the production source exactly"

    Set-Content -LiteralPath $source -Value "pub fn updated_source_bound() {}" -NoNewline
    Assert-True (
        (Get-Content -LiteralPath $linkedSource -Raw) -eq "pub fn updated_source_bound() {}"
    ) "the extraction view follows subsequent production-source updates"

    & $setupScript -RepositoryRoot $repository -WorkspacePath $workspace -ValidateOnly | Out-Null
    & $setupScript -RepositoryRoot $repository -WorkspacePath $workspace | Out-Null

    $wrongManifestWorkspace = Join-Path $cache "wrong-manifest"
    [IO.Directory]::CreateDirectory($wrongManifestWorkspace) | Out-Null
    Set-Content -LiteralPath (Join-Path $wrongManifestWorkspace "Cargo.toml") `
        -Value "[package]`nname = 'wrong'" -NoNewline
    Assert-Throws {
        & $setupScript -RepositoryRoot $repository -WorkspacePath $wrongManifestWorkspace | Out-Null
    } "does not match" "an existing non-template Cargo manifest is rejected"

    $copiedSourceWorkspace = Join-Path $cache "copied-source"
    & $setupScript -RepositoryRoot $repository -WorkspacePath $copiedSourceWorkspace | Out-Null
    $copiedSource = Join-Path $copiedSourceWorkspace "src\lib.rs"
    Remove-Item -LiteralPath $copiedSource
    Copy-Item -LiteralPath $source -Destination $copiedSource
    Assert-Throws {
        & $setupScript -RepositoryRoot $repository -WorkspacePath $copiedSourceWorkspace `
            -ValidateOnly | Out-Null
    } "must be a hard link" "an identical copied source file is rejected"

    $wrongTarget = Join-Path $sourceDirectory "wrong.rs"
    Copy-Item -LiteralPath $source -Destination $wrongTarget
    $wrongTargetWorkspace = Join-Path $cache "wrong-target"
    & $setupScript -RepositoryRoot $repository -WorkspacePath $wrongTargetWorkspace | Out-Null
    $wrongTargetLink = Join-Path $wrongTargetWorkspace "src\lib.rs"
    Remove-Item -LiteralPath $wrongTargetLink
    New-Item -ItemType HardLink -Path $wrongTargetLink -Target $wrongTarget | Out-Null
    Assert-Throws {
        & $setupScript -RepositoryRoot $repository -WorkspacePath $wrongTargetWorkspace `
            -ValidateOnly | Out-Null
    } "not production source" "a same-content hard link to the wrong source is rejected"

    $junctionWorkspace = Join-Path $cache "junction-source"
    & $setupScript -RepositoryRoot $repository -WorkspacePath $junctionWorkspace | Out-Null
    $junctionSource = Join-Path $junctionWorkspace "src"
    Remove-Item -LiteralPath (Join-Path $junctionSource "lib.rs")
    Remove-Item -LiteralPath $junctionSource
    $junctionTarget = Join-Path $testRoot "junction-target"
    [IO.Directory]::CreateDirectory($junctionTarget) | Out-Null
    New-Item -ItemType Junction -Path $junctionSource -Target $junctionTarget | Out-Null
    Assert-Throws {
        & $setupScript -RepositoryRoot $repository -WorkspacePath $junctionWorkspace | Out-Null
    } "must be a physical directory" "a junction cannot redirect extraction source creation"

    $outsideCache = Join-Path $repository "extraction-workspace"
    Assert-Throws {
        & $setupScript -RepositoryRoot $repository -WorkspacePath $outsideCache | Out-Null
    } "must be a direct child" "a workspace outside the repository cache is rejected"

    $nestedWorkspace = Join-Path $cache "nested\workspace"
    Assert-Throws {
        & $setupScript -RepositoryRoot $repository -WorkspacePath $nestedWorkspace | Out-Null
    } "must be a direct child" "a nested workspace cannot bypass the physical cache boundary"

    $missingWorkspace = Join-Path $cache "missing"
    Assert-Throws {
        & $setupScript -RepositoryRoot $repository -WorkspacePath $missingWorkspace `
            -ValidateOnly | Out-Null
    } "does not exist" "validate-only mode rejects a missing workspace"

    Write-Output "setup-extraction-workspace behavioral tests passed"
} finally {
    $resolvedTestRoot = [IO.Path]::GetFullPath($testRoot)
    $temporaryRoot = [IO.Path]::GetFullPath([IO.Path]::GetTempPath()).TrimEnd(
        [IO.Path]::DirectorySeparatorChar,
        [IO.Path]::AltDirectorySeparatorChar
    ) + [IO.Path]::DirectorySeparatorChar
    if (-not $resolvedTestRoot.StartsWith($temporaryRoot, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Refusing to remove test data outside the operating-system temporary directory."
    }
    if (Test-Path -LiteralPath $resolvedTestRoot) {
        Remove-Item -LiteralPath $resolvedTestRoot -Recurse -Force
    }
}
