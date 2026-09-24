[CmdletBinding()]
param(
    [string]$Suite = ".upstream/nagini",
    [string]$NaginiSource = ".upstream/nagini/src",
    [string]$CargoPath = "cargo",
    [string]$PythonPath = "python"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$requirementsPath = Join-Path $repositoryRoot "conformance/release-completion-v1.json"
$requirements = Get-Content -LiteralPath $requirementsPath -Raw | ConvertFrom-Json -ErrorAction Stop
if ($requirements.schema -cne "maledictus-release-completion/v1") {
    throw "unexpected release requirements schema: $($requirements.schema)"
}
if ([System.Environment]::OSVersion.Platform -ne [System.PlatformID]::Win32NT) {
    throw "the release-completion gate must run on Windows because it verifies the Windows package"
}

$repositoryCache = Join-Path $repositoryRoot ".cache"
if (-not (Test-Path -LiteralPath $repositoryCache)) {
    New-Item -ItemType Directory -Path $repositoryCache -Force | Out-Null
}
$repositoryCache = (Resolve-Path -LiteralPath $repositoryCache).Path
$cachePrefix = $repositoryCache.TrimEnd("\") + "\"
$releaseRoot = Join-Path $repositoryCache "release"
New-Item -ItemType Directory -Path $releaseRoot -Force | Out-Null

function Resolve-RepositoryPath {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Relative,
        [Parameter(Mandatory = $true)]
        [string]$Description
    )

    if ([System.IO.Path]::IsPathRooted($Relative)) {
        throw "$Description must be repository-relative: $Relative"
    }
    $resolved = [System.IO.Path]::GetFullPath((Join-Path $repositoryRoot $Relative))
    $repositoryPrefix = $repositoryRoot.TrimEnd("\") + "\"
    if (-not $resolved.StartsWith($repositoryPrefix, [System.StringComparison]::OrdinalIgnoreCase)) {
        throw "$Description escapes the repository: $resolved"
    }
    return $resolved
}

$packageDestination = Resolve-RepositoryPath `
    ([string]$requirements.windows_package.destination) `
    "release package destination"
if (-not $packageDestination.StartsWith($cachePrefix, [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "release package destination must be below repository .cache: $packageDestination"
}
$examplesRoot = Resolve-RepositoryPath ([string]$requirements.examples.root) "example root"
$coveragePath = Resolve-RepositoryPath ([string]$requirements.formal.coverage) "coverage artifact"
$coverageConfig = Resolve-RepositoryPath ([string]$requirements.formal.config) "coverage configuration"
$coverageTool = Resolve-RepositoryPath ([string]$requirements.formal.tool_manifest) "coverage tool manifest"
$pinPath = Resolve-RepositoryPath ([string]$requirements.classification.pin) "classification pin"
$classificationReport = Join-Path $releaseRoot "classification.json"
$cargoTarget = Join-Path $releaseRoot "cargo-target"
$suitePath = if ([System.IO.Path]::IsPathRooted($Suite)) {
    [System.IO.Path]::GetFullPath($Suite)
} else {
    [System.IO.Path]::GetFullPath((Join-Path $repositoryRoot $Suite))
}
$naginiSourcePath = if ([System.IO.Path]::IsPathRooted($NaginiSource)) {
    [System.IO.Path]::GetFullPath($NaginiSource)
} else {
    [System.IO.Path]::GetFullPath((Join-Path $repositoryRoot $NaginiSource))
}

$priorTarget = $env:CARGO_TARGET_DIR
Push-Location $repositoryRoot
try {
    $env:CARGO_TARGET_DIR = $cargoTarget

    & (Join-Path $PSScriptRoot "package-windows.ps1") `
        -Profile release `
        -CargoPath $CargoPath `
        -Destination $packageDestination `
        -PythonPath $PythonPath `
        -NaginiSource $naginiSourcePath

    & (Join-Path $PSScriptRoot "verify-windows-package.ps1") `
        -Destination $packageDestination `
        -ExamplesRoot $examplesRoot `
        -NaginiSource $naginiSourcePath

    $packageManifestPath = Join-Path $packageDestination "package-manifest.json"
    $packageManifest = Get-Content -LiteralPath $packageManifestPath -Raw |
        ConvertFrom-Json -ErrorAction Stop
    if ($packageManifest.schema -cne [string]$requirements.windows_package.manifest_schema -or
        $packageManifest.profile -cne [string]$requirements.windows_package.profile) {
        throw (
            "Windows package identity does not match the release requirements: " +
            "schema=$($packageManifest.schema), profile=$($packageManifest.profile)"
        )
    }

    $executable = Join-Path $packageDestination ([string]$requirements.windows_package.executable)
    $libz3 = Join-Path $packageDestination ([string]$requirements.windows_package.libz3)
    & (Join-Path $PSScriptRoot "classify-suite.ps1") `
        -Executable $executable `
        -LibZ3 $libz3 `
        -Suite $suitePath `
        -Pin $pinPath `
        -Output $classificationReport

    & $CargoPath run --quiet --offline --manifest-path $coverageTool -- `
        check `
        --project $repositoryRoot `
        --config $coverageConfig `
        --output $coveragePath
    if ($LASTEXITCODE -ne 0) {
        throw "formal coverage currentness check failed with exit code $LASTEXITCODE"
    }
} finally {
    $env:CARGO_TARGET_DIR = $priorTarget
    Pop-Location
}

& (Join-Path $PSScriptRoot "assert-release-evidence.ps1") `
    -Requirements $requirementsPath `
    -ClassificationReport $classificationReport `
    -CoverageReport $coveragePath `
    -ExamplesRoot $examplesRoot

Write-Output "Maledictus release-completion gate passed"
