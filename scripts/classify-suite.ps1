[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [string]$Executable,

    [Parameter(Mandatory = $true)]
    [string]$Suite,

    [Parameter(Mandatory = $true)]
    [string]$Pin,

    [string]$LibZ3,

    [string]$CacheRoot,

    [string]$Output
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Resolve-RegularFile {
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
    return $resolved
}

function Resolve-BeforeCreation {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Path
    )

    $cursor = [System.IO.Path]::GetFullPath($Path)
    $missing = [System.Collections.Generic.List[string]]::new()
    while (-not (Test-Path -LiteralPath $cursor)) {
        $leaf = Split-Path -Leaf $cursor
        if ([string]::IsNullOrEmpty($leaf)) {
            throw "classifier cache path has no existing ancestor: $Path"
        }
        $missing.Add($leaf)
        $cursor = Split-Path -Parent $cursor
    }

    $resolved = (Resolve-Path -LiteralPath $cursor -ErrorAction Stop).Path
    for ($index = $missing.Count - 1; $index -ge 0; $index--) {
        $resolved = Join-Path $resolved $missing[$index]
    }
    return [System.IO.Path]::GetFullPath($resolved)
}

function Assert-PathBelow {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Path,

        [Parameter(Mandatory = $true)]
        [string]$Parent,

        [Parameter(Mandatory = $true)]
        [string]$Description
    )

    $separator = [System.IO.Path]::DirectorySeparatorChar
    $normalizedPath = [System.IO.Path]::GetFullPath($Path).TrimEnd($separator)
    $normalizedParent = [System.IO.Path]::GetFullPath($Parent).TrimEnd($separator)
    $prefix = $normalizedParent + $separator
    if (-not $normalizedPath.StartsWith($prefix, [System.StringComparison]::OrdinalIgnoreCase)) {
        throw "$Description must be below repository .cache: $normalizedPath"
    }
}

function Find-LibZ3 {
    param(
        [Parameter(Mandatory = $true)]
        [string]$ExecutablePath,

        [string]$RequestedPath
    )

    if (-not [string]::IsNullOrWhiteSpace($RequestedPath)) {
        return Resolve-RegularFile $RequestedPath "libz3.dll"
    }

    $candidates = [System.Collections.Generic.List[string]]::new()
    $candidates.Add((Join-Path (Split-Path -Parent $ExecutablePath) "libz3.dll"))
    $candidates.Add((Join-Path (Get-Location).Path "libz3.dll"))
    foreach ($directory in ($env:PATH -split [System.IO.Path]::PathSeparator)) {
        if (-not [string]::IsNullOrWhiteSpace($directory)) {
            $candidates.Add((Join-Path $directory "libz3.dll"))
        }
    }
    foreach ($candidate in $candidates) {
        if (Test-Path -LiteralPath $candidate -PathType Leaf) {
            return Resolve-RegularFile $candidate "libz3.dll"
        }
    }
    throw "cannot locate libz3.dll; pass its exact path with -LibZ3"
}

function Assert-Snapshot {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Directory,

        [Parameter(Mandatory = $true)]
        [string]$ExecutableSha256,

        [Parameter(Mandatory = $true)]
        [string]$LibZ3Sha256
    )

    $directoryItem = Get-Item -LiteralPath $Directory -Force
    if (-not $directoryItem.PSIsContainer -or
        ($directoryItem.Attributes -band [System.IO.FileAttributes]::ReparsePoint)) {
        throw "classifier snapshot is not a regular directory: $Directory"
    }
    $snapshotExecutable = Resolve-RegularFile (Join-Path $Directory "maledictus.exe") "classifier snapshot executable"
    $snapshotLibZ3 = Resolve-RegularFile (Join-Path $Directory "libz3.dll") "classifier snapshot libz3.dll"
    $manifestPath = Resolve-RegularFile (Join-Path $Directory "snapshot.json") "classifier snapshot manifest"
    $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
    if ($manifest.schema -ne "maledictus-classifier-binary-snapshot/v1" -or
        $manifest.executable_sha256 -ne $ExecutableSha256 -or
        $manifest.libz3_sha256 -ne $LibZ3Sha256 -or
        (Get-FileHash -LiteralPath $snapshotExecutable -Algorithm SHA256).Hash.ToLowerInvariant() -ne $ExecutableSha256 -or
        (Get-FileHash -LiteralPath $snapshotLibZ3 -Algorithm SHA256).Hash.ToLowerInvariant() -ne $LibZ3Sha256) {
        throw "classifier snapshot content does not match its declared immutable identity: $Directory"
    }
}

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$repositoryCache = Join-Path $repositoryRoot ".cache"
if (-not (Test-Path -LiteralPath $repositoryCache)) {
    New-Item -ItemType Directory -Path $repositoryCache -Force | Out-Null
}
$repositoryCache = (Resolve-Path -LiteralPath $repositoryCache).Path
Assert-PathBelow $repositoryCache $repositoryRoot "repository .cache"

$sourceExecutable = Resolve-RegularFile $Executable "classifier executable"
$sourceLibZ3 = Find-LibZ3 $sourceExecutable $LibZ3
$suiteRoot = (Resolve-Path -LiteralPath $Suite -ErrorAction Stop).Path
$pinPath = Resolve-RegularFile $Pin "classifier suite pin"

if ([string]::IsNullOrWhiteSpace($CacheRoot)) {
    $CacheRoot = Join-Path $repositoryCache "classifier-bin"
}
$resolvedCacheRoot = Resolve-BeforeCreation $CacheRoot
Assert-PathBelow $resolvedCacheRoot $repositoryCache "classifier binary cache"
if (-not (Test-Path -LiteralPath $resolvedCacheRoot)) {
    New-Item -ItemType Directory -Path $resolvedCacheRoot -Force | Out-Null
}
$resolvedCacheRoot = (Resolve-Path -LiteralPath $resolvedCacheRoot).Path
Assert-PathBelow $resolvedCacheRoot $repositoryCache "classifier binary cache"

$executableSha256 = (Get-FileHash -LiteralPath $sourceExecutable -Algorithm SHA256).Hash.ToLowerInvariant()
$libZ3Sha256 = (Get-FileHash -LiteralPath $sourceLibZ3 -Algorithm SHA256).Hash.ToLowerInvariant()
$snapshotDirectory = Join-Path $resolvedCacheRoot $executableSha256

if (-not (Test-Path -LiteralPath $snapshotDirectory)) {
    $stagingDirectory = Join-Path $resolvedCacheRoot (".stage-{0}-{1}" -f $executableSha256, [guid]::NewGuid().ToString("N"))
    New-Item -ItemType Directory -Path $stagingDirectory | Out-Null
    try {
        Copy-Item -LiteralPath $sourceExecutable -Destination (Join-Path $stagingDirectory "maledictus.exe")
        Copy-Item -LiteralPath $sourceLibZ3 -Destination (Join-Path $stagingDirectory "libz3.dll")
        $manifest = [ordered]@{
            schema = "maledictus-classifier-binary-snapshot/v1"
            executable_sha256 = $executableSha256
            libz3_sha256 = $libZ3Sha256
        } | ConvertTo-Json
        $utf8WithoutBom = [System.Text.UTF8Encoding]::new($false)
        [System.IO.File]::WriteAllText((Join-Path $stagingDirectory "snapshot.json"), $manifest + [Environment]::NewLine, $utf8WithoutBom)
        Assert-Snapshot $stagingDirectory $executableSha256 $libZ3Sha256
        try {
            [System.IO.Directory]::Move($stagingDirectory, $snapshotDirectory)
            [Console]::Error.WriteLine("[classifier-launcher] published binary snapshot $snapshotDirectory")
        }
        catch {
            if (-not (Test-Path -LiteralPath $snapshotDirectory -PathType Container)) {
                throw
            }
        }
    }
    finally {
        if (Test-Path -LiteralPath $stagingDirectory) {
            Remove-Item -LiteralPath $stagingDirectory -Recurse -Force
        }
    }
}

Assert-Snapshot $snapshotDirectory $executableSha256 $libZ3Sha256
$snapshotExecutable = Join-Path $snapshotDirectory "maledictus.exe"
[Console]::Error.WriteLine("[classifier-launcher] running immutable executable $snapshotExecutable")
if ([string]::IsNullOrWhiteSpace($Output)) {
    & $snapshotExecutable conformance classify-suite --suite $suiteRoot --pin $pinPath
    exit $LASTEXITCODE
}

$outputPath = Resolve-BeforeCreation $Output
Assert-PathBelow $outputPath $repositoryCache "classifier report output"
$report = & $snapshotExecutable conformance classify-suite --suite $suiteRoot --pin $pinPath
if ($LASTEXITCODE -ne 0) {
    exit $LASTEXITCODE
}
$reportText = ($report -join [Environment]::NewLine).Trim()
try {
    $null = $reportText | ConvertFrom-Json -ErrorAction Stop
}
catch {
    throw "classifier produced malformed JSON; report was not written: $($_.Exception.Message)"
}
$outputParent = Split-Path -Parent $outputPath
if (-not (Test-Path -LiteralPath $outputParent)) {
    New-Item -ItemType Directory -Path $outputParent -Force | Out-Null
}
$utf8WithoutBom = [System.Text.UTF8Encoding]::new($false)
[System.IO.File]::WriteAllText($outputPath, $reportText + [Environment]::NewLine, $utf8WithoutBom)
[Console]::Error.WriteLine("[classifier-launcher] wrote report $outputPath")
