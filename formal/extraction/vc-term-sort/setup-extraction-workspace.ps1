param(
    [string]$RepositoryRoot,
    [string]$WorkspacePath,
    [switch]$ValidateOnly
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

function Get-NormalizedPath {
    param([Parameter(Mandatory = $true)][string]$Path)

    return [IO.Path]::GetFullPath($Path).TrimEnd(
        [IO.Path]::DirectorySeparatorChar,
        [IO.Path]::AltDirectorySeparatorChar
    )
}

function Test-IsDirectChild {
    param(
        [Parameter(Mandatory = $true)][string]$Candidate,
        [Parameter(Mandatory = $true)][string]$Parent
    )

    $normalizedCandidate = Get-NormalizedPath $Candidate
    $normalizedParent = Get-NormalizedPath $Parent
    $candidateParent = Get-NormalizedPath ([IO.Path]::GetDirectoryName($normalizedCandidate))
    return $candidateParent.Equals(
        $normalizedParent,
        [StringComparison]::OrdinalIgnoreCase
    )
}

function Assert-PhysicalDirectory {
    param(
        [Parameter(Mandatory = $true)][string]$Path,
        [Parameter(Mandatory = $true)][string]$Description
    )

    if (-not (Test-Path -LiteralPath $Path)) {
        return
    }
    if (-not (Test-Path -LiteralPath $Path -PathType Container)) {
        throw "$Description is not a directory: $Path"
    }
    $directory = Get-Item -LiteralPath $Path -Force
    if (-not [string]::IsNullOrEmpty([string]$directory.LinkType)) {
        throw "$Description must be a physical directory, not $($directory.LinkType): $Path"
    }
}

function Assert-ExactFile {
    param(
        [Parameter(Mandatory = $true)][string]$Actual,
        [Parameter(Mandatory = $true)][string]$Expected,
        [Parameter(Mandatory = $true)][string]$Description
    )

    if (-not (Test-Path -LiteralPath $Actual -PathType Leaf)) {
        throw "Missing $Description at $Actual."
    }
    $actualHash = (Get-FileHash -LiteralPath $Actual -Algorithm SHA256).Hash
    $expectedHash = (Get-FileHash -LiteralPath $Expected -Algorithm SHA256).Hash
    if ($actualHash -ne $expectedHash) {
        throw "$Description at $Actual does not match $Expected. Refusing to overwrite it."
    }
}

$scriptRoot = Get-NormalizedPath $PSScriptRoot
if ([string]::IsNullOrWhiteSpace($RepositoryRoot)) {
    $RepositoryRoot = Join-Path $scriptRoot "..\..\.."
}
$repository = Get-NormalizedPath $RepositoryRoot
if (-not (Test-Path -LiteralPath $repository -PathType Container)) {
    throw "Repository root does not exist: $repository"
}
Assert-PhysicalDirectory -Path $repository -Description "repository root"

$cacheRoot = Get-NormalizedPath (Join-Path $repository ".cache")
if ([string]::IsNullOrWhiteSpace($WorkspacePath)) {
    $WorkspacePath = Join-Path $cacheRoot "vc-term-sort-extraction"
}
$workspace = Get-NormalizedPath $WorkspacePath
if (-not (Test-IsDirectChild -Candidate $workspace -Parent $cacheRoot)) {
    throw "Extraction workspace must be a direct child of the repository cache directory: $cacheRoot"
}
Assert-PhysicalDirectory -Path $cacheRoot -Description "repository cache"
Assert-PhysicalDirectory -Path $workspace -Description "extraction workspace"

$source = Get-NormalizedPath (Join-Path $repository "src\vc.rs")
$templateManifest = Get-NormalizedPath (Join-Path $scriptRoot "Cargo.toml")
if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
    throw "Production Term::sort source does not exist: $source"
}
if (-not (Test-Path -LiteralPath $templateManifest -PathType Leaf)) {
    throw "Extraction Cargo template does not exist: $templateManifest"
}

$workspaceManifest = Join-Path $workspace "Cargo.toml"
$workspaceSourceDirectory = Join-Path $workspace "src"
$workspaceSource = Join-Path $workspaceSourceDirectory "lib.rs"
Assert-PhysicalDirectory -Path $workspaceSourceDirectory `
    -Description "extraction source directory"

if ($ValidateOnly) {
    if (-not (Test-Path -LiteralPath $workspace -PathType Container)) {
        throw "Extraction workspace does not exist: $workspace"
    }
} else {
    [IO.Directory]::CreateDirectory($workspace) | Out-Null
    [IO.Directory]::CreateDirectory($workspaceSourceDirectory) | Out-Null
    Assert-PhysicalDirectory -Path $workspace -Description "extraction workspace"
    Assert-PhysicalDirectory -Path $workspaceSourceDirectory `
        -Description "extraction source directory"
    if (-not (Test-Path -LiteralPath $workspaceManifest)) {
        [IO.File]::Copy($templateManifest, $workspaceManifest, $false)
    }
}

Assert-ExactFile -Actual $workspaceManifest -Expected $templateManifest `
    -Description "extraction Cargo manifest"

if (-not (Test-Path -LiteralPath $workspaceSource)) {
    if ($ValidateOnly) {
        throw "Extraction source hard link does not exist: $workspaceSource"
    }
    [IO.Directory]::CreateDirectory($workspaceSourceDirectory) | Out-Null
    New-Item -ItemType HardLink -Path $workspaceSource -Target $source | Out-Null
}

if (-not (Test-Path -LiteralPath $workspaceSource -PathType Leaf)) {
    throw "Extraction source path is not a file: $workspaceSource"
}
$link = Get-Item -LiteralPath $workspaceSource -Force
if ($link.LinkType -ne "HardLink") {
    throw "Extraction source must be a hard link, not a copied or symbolic file: $workspaceSource"
}

$expectedTarget = Get-NormalizedPath $source
$actualTargets = @($link.Target | ForEach-Object { Get-NormalizedPath ([string]$_) })
$hasExpectedTarget = $actualTargets | Where-Object {
    $_.Equals($expectedTarget, [StringComparison]::OrdinalIgnoreCase)
}
if (-not $hasExpectedTarget) {
    $renderedTargets = $actualTargets -join ", "
    throw "Extraction source hard link targets [$renderedTargets], not production source $expectedTarget."
}

Assert-ExactFile -Actual $workspaceSource -Expected $source `
    -Description "extraction source hard link"

Write-Output "vc-term-sort extraction workspace valid"
Write-Output "workspace: $workspace"
Write-Output "source hard link: $workspaceSource -> $source"
