param(
    [Parameter(Mandatory = $true)]
    [string] $Project,

    [Parameter(Mandatory = $true)]
    [string] $LakePath,

    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]] $LakeArguments
)

$ErrorActionPreference = "Stop"

if (!$LakeArguments -or $LakeArguments.Count -eq 0) {
    throw "at least one Lake command argument is required"
}

if (Test-Path -LiteralPath $LakePath) {
    $LakePath = (Resolve-Path -LiteralPath $LakePath).Path
}
else {
    $lakeCommand = Get-Command -Name $LakePath -CommandType Application -ErrorAction Stop
    $LakePath = $lakeCommand.Source
}

$bundledElanHome = Split-Path -Parent (Split-Path -Parent $LakePath)
$useBundledElanHome = Test-Path -LiteralPath (Join-Path $bundledElanHome "settings.toml")

$workspace = Split-Path -Parent $PSScriptRoot
$workspace = [System.IO.Path]::GetFullPath($workspace)
$cacheRoot = [System.IO.Path]::GetFullPath((Join-Path $workspace ".cache"))
$cachePrefix = $cacheRoot + [System.IO.Path]::DirectorySeparatorChar
$pathComparison = [System.StringComparison]::Ordinal
if ($IsWindows -or $env:OS -eq "Windows_NT") {
    $pathComparison = [System.StringComparison]::OrdinalIgnoreCase
}

function Resolve-WorkspacePath {
    param(
        [Parameter(Mandatory = $true)]
        [string] $Path
    )

    return [System.IO.Path]::GetFullPath((Join-Path $workspace $Path))
}

function Convert-ToLakePath {
    param(
        [Parameter(Mandatory = $true)]
        [string] $Path
    )

    return $Path.Replace([System.IO.Path]::DirectorySeparatorChar, "/")
}

function Get-RelativeConfiguredPath {
    param(
        [Parameter(Mandatory = $true)]
        [string] $FromDirectory,
        [Parameter(Mandatory = $true)]
        [string] $ToPath
    )

    $separator = [System.IO.Path]::DirectorySeparatorChar
    $fromWithSeparator = $FromDirectory.TrimEnd($separator) + $separator
    $fromUri = [System.Uri]::new($fromWithSeparator)
    $toUri = [System.Uri]::new($ToPath)
    return [System.Uri]::UnescapeDataString($fromUri.MakeRelativeUri($toUri).ToString())
}

$registryPath = Join-Path $PSScriptRoot "lake-projects.json"
$registry = Get-Content -LiteralPath $registryPath -Raw | ConvertFrom-Json
if ($registry.schema -ne "maledictus-lake-projects/v1") {
    throw "unsupported Lake project registry schema: $($registry.schema)"
}
$matches = @($registry.projects | Where-Object { $_.id -eq $Project })
if ($matches.Count -ne 1) {
    throw "unknown or duplicate Lake project id: $Project"
}
$entry = $matches[0]

$projectDirectory = Resolve-WorkspacePath -Path $entry.directory
$configPath = Resolve-WorkspacePath -Path $entry.config
$manifestPath = Resolve-WorkspacePath -Path $entry.manifest
$toolchainPath = Resolve-WorkspacePath -Path $entry.toolchain
$packagesPath = Resolve-WorkspacePath -Path $entry.packages
$buildPath = Resolve-WorkspacePath -Path $entry.build
foreach ($cachePath in @($packagesPath, $buildPath)) {
    if (!$cachePath.StartsWith($cachePrefix, $pathComparison)) {
        throw "Lake project $Project resolves repository-local output outside .cache: $cachePath"
    }
}

$stageRoot = Join-Path $cacheRoot (
    "lake/workspaces/$Project/" + [System.Guid]::NewGuid().ToString("N")
)
$stageRoot = [System.IO.Path]::GetFullPath($stageRoot)
if (!$stageRoot.StartsWith($cachePrefix, $pathComparison)) {
    throw "refusing to stage Lake outside repository cache: $stageRoot"
}

New-Item -ItemType Directory -Path $stageRoot -Force | Out-Null
try {
    $configName = Split-Path -Leaf $configPath
    $stageConfig = Join-Path $stageRoot $configName
    $configText = [System.IO.File]::ReadAllText($configPath)
    $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
    $configuredPackages = $manifest.packagesDir.Replace("\\", "/")
    $configuredBuild = Get-RelativeConfiguredPath `
        -FromDirectory $projectDirectory `
        -ToPath $buildPath
    $absolutePackages = Convert-ToLakePath -Path $packagesPath
    $absoluteBuild = Convert-ToLakePath -Path $buildPath
    $packagesDeclaration = "packagesDir = `"$configuredPackages`""
    $buildDeclaration = "buildDir = `"$configuredBuild`""
    if (!$configText.Contains($packagesDeclaration)) {
        throw "$Project config does not contain its manifest-bound packagesDir declaration"
    }
    if (!$configText.Contains($buildDeclaration)) {
        throw "$Project config does not contain its registry-bound buildDir declaration"
    }
    $stageConfigText = $configText.Replace(
        $packagesDeclaration,
        "packagesDir = `"$absolutePackages`""
    ).Replace(
        $buildDeclaration,
        "buildDir = `"$absoluteBuild`""
    )
    [System.IO.File]::WriteAllText($stageConfig, $stageConfigText)

    $manifest.packagesDir = $absolutePackages
    [System.IO.File]::WriteAllText(
        (Join-Path $stageRoot "lake-manifest.json"),
        ($manifest | ConvertTo-Json -Depth 100)
    )
    Copy-Item -LiteralPath $toolchainPath -Destination (Join-Path $stageRoot "lean-toolchain")

    foreach ($sourceEntry in $entry.sources) {
        $sourcePath = Resolve-WorkspacePath -Path $sourceEntry
        $destination = Join-Path $stageRoot (Split-Path -Leaf $sourcePath)
        Copy-Item -LiteralPath $sourcePath -Destination $destination -Recurse
    }

    $toolchain = (Get-Content -LiteralPath $toolchainPath -Raw).Trim()
    $previousToolchain = $env:ELAN_TOOLCHAIN
    $previousElanHome = $env:ELAN_HOME
    $env:ELAN_TOOLCHAIN = $toolchain
    if ($useBundledElanHome) {
        $env:ELAN_HOME = $bundledElanHome
    }
    Push-Location $stageRoot
    try {
        & $LakePath --dir $stageRoot @LakeArguments
        $lakeExitCode = $LASTEXITCODE
    }
    finally {
        Pop-Location
        $env:ELAN_TOOLCHAIN = $previousToolchain
        $env:ELAN_HOME = $previousElanHome
    }
}
finally {
    if (Test-Path -LiteralPath $stageRoot) {
        $resolvedStage = (Resolve-Path -LiteralPath $stageRoot).Path
        if (!$resolvedStage.StartsWith($cachePrefix, $pathComparison)) {
            throw "refusing to clean Lake staging directory outside .cache: $resolvedStage"
        }
        Remove-Item -LiteralPath $resolvedStage -Recurse -Force
    }
}

exit $lakeExitCode
