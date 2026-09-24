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

$workspace = Split-Path -Parent $PSScriptRoot
$workspace = [System.IO.Path]::GetFullPath($workspace)
$cacheRoot = [System.IO.Path]::GetFullPath((Join-Path $workspace ".cache"))
$cachePrefix = $cacheRoot + [System.IO.Path]::DirectorySeparatorChar
$toolchainsRoot = [System.IO.Path]::GetFullPath((Join-Path $workspace ".toolchains"))
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

function Resolve-ConfiguredPath {
    param(
        [Parameter(Mandatory = $true)]
        [string] $ProjectDirectory,
        [Parameter(Mandatory = $true)]
        [string] $ConfiguredPath
    )

    return [System.IO.Path]::GetFullPath((Join-Path $ProjectDirectory $ConfiguredPath))
}

function Assert-UnderCache {
    param(
        [Parameter(Mandatory = $true)]
        [string] $Path,
        [Parameter(Mandatory = $true)]
        [string] $Description
    )

    $resolved = [System.IO.Path]::GetFullPath($Path)
    if (!$resolved.StartsWith($cachePrefix, $pathComparison)) {
        throw "$Description resolves outside the repository cache: $resolved"
    }
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
if ($registry.projects.Count -eq 0) {
    throw "Lake project registry is empty"
}

$expectedConfigs = @{}
foreach ($project in $registry.projects) {
    $resolvedConfig = Resolve-WorkspacePath -Path $project.config
    if ($expectedConfigs.ContainsKey($resolvedConfig)) {
        throw "duplicate Lake config in project registry: $resolvedConfig"
    }
    $expectedConfigs[$resolvedConfig] = $true
}
$discoveredConfigs = @(Get-ChildItem -LiteralPath (Join-Path $workspace "formal") -Recurse -File |
    Where-Object {
        ($_.Name -eq "lakefile.lean" -or $_.Name -eq "lakefile.toml") -and
        !$_.FullName.Contains(
            "$([System.IO.Path]::DirectorySeparatorChar).lake$([System.IO.Path]::DirectorySeparatorChar)"
        )
    })
foreach ($config in $discoveredConfigs) {
    $resolvedConfig = [System.IO.Path]::GetFullPath($config.FullName)
    if (!$expectedConfigs.ContainsKey($resolvedConfig)) {
        throw "formal Lake project is not integrated with the centralized runner: $resolvedConfig"
    }
}
if ($discoveredConfigs.Count -ne $expectedConfigs.Count) {
    throw "formal Lake project discovery count does not match the centralized registry"
}

$hostExecutable = (Get-Process -Id $PID).Path
$runner = Join-Path $PSScriptRoot "run-lake.ps1"
foreach ($project in $registry.projects) {
    $projectDirectory = Resolve-WorkspacePath -Path $project.directory
    $configPath = Resolve-WorkspacePath -Path $project.config
    $manifestPath = Resolve-WorkspacePath -Path $project.manifest
    $expectedPackages = Resolve-WorkspacePath -Path $project.packages
    $expectedBuild = Resolve-WorkspacePath -Path $project.build
    Assert-UnderCache -Path $expectedPackages -Description "$($project.id) packagesDir"
    Assert-UnderCache -Path $expectedBuild -Description "$($project.id) buildDir"

    $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
    $manifestPackages = Resolve-ConfiguredPath `
        -ProjectDirectory $projectDirectory `
        -ConfiguredPath $manifest.packagesDir
    if (!$manifestPackages.Equals($expectedPackages, $pathComparison)) {
        throw "Lake manifest for $($project.id) resolves packagesDir to $manifestPackages, expected $expectedPackages"
    }

    $configuredBuild = Get-RelativeConfiguredPath `
        -FromDirectory $projectDirectory `
        -ToPath $expectedBuild
    $configText = [System.IO.File]::ReadAllText($configPath)
    $configuredPackages = $manifest.packagesDir.Replace("\\", "/")
    if (!$configText.Contains("packagesDir = `"$configuredPackages`"")) {
        throw "$($project.id) config does not declare its manifest-bound packagesDir"
    }
    if (!$configText.Contains("buildDir = `"$configuredBuild`"")) {
        throw "$($project.id) config does not declare its registry-bound buildDir"
    }

    $lakeOutput = & $runner `
        -Project $project.id `
        -LakePath $LakePath `
        env $hostExecutable -NoProfile -Command `
            "[Environment]::GetEnvironmentVariable('LEAN_PATH')" 2>&1 | Out-String
    $runnerExitCode = $LASTEXITCODE
    if ($runnerExitCode -ne 0) {
        throw "central Lake runner could not load $($project.id):`n$lakeOutput"
    }
    if ($lakeOutput.Contains("manifest out of date")) {
        throw "Lake reports a stale packagesDir for $($project.id):`n$lakeOutput"
    }

    $leanPathLine = ($lakeOutput -split "`r?`n" |
        Where-Object { $_.Contains([System.IO.Path]::PathSeparator) } |
        Select-Object -Last 1)
    if (!$leanPathLine) {
        throw "Lake did not return LEAN_PATH for $($project.id):`n$lakeOutput"
    }
    $resolvedLeanPaths = @(
        ($leanPathLine -split [System.IO.Path]::PathSeparator) |
            ForEach-Object { [System.IO.Path]::GetFullPath($_) }
    )
    $expectedBuildLibrary = [System.IO.Path]::GetFullPath(
        (Join-Path $expectedBuild "lib/lean")
    )
    if (!($resolvedLeanPaths | Where-Object {
        $_.Equals($expectedBuildLibrary, $pathComparison)
    })) {
        throw "Lake resolved $($project.id) build output outside its configured cache path. LEAN_PATH=$leanPathLine"
    }
    foreach ($leanPath in $resolvedLeanPaths) {
        if ($leanPath.StartsWith($workspace, $pathComparison) -and
            !$leanPath.StartsWith($toolchainsRoot, $pathComparison)) {
            Assert-UnderCache `
                -Path $leanPath `
                -Description "$($project.id) repository-local LEAN_PATH entry"
        }
    }
}

$legacyLakeDirectories = @(Get-ChildItem `
    -LiteralPath (Join-Path $workspace "formal") `
    -Recurse `
    -Directory `
    -Force `
    -Filter ".lake" `
    -ErrorAction SilentlyContinue)
if ($legacyLakeDirectories.Count -ne 0) {
    throw (
        "repository-local .lake directories are forbidden; use formal/run-lake.ps1: " +
        (($legacyLakeDirectories | Select-Object -ExpandProperty FullName) -join ", ")
    )
}

Write-Output "Lake cache hygiene passed for $($registry.projects.Count) centrally staged projects."
