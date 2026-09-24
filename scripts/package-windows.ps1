param(
    [ValidateSet("debug", "release")]
    [string]$Profile = "release",
    [string]$CargoPath = "cargo",
    [string]$Destination = ".cache/release/windows-x86_64",
    [string]$PythonPath = "python",
    [string]$PythonVersion = "3.12.10",
    [string]$NaginiSource = ".upstream/nagini/src"
)

$ErrorActionPreference = "Stop"

. (Join-Path $PSScriptRoot "package-input-snapshot.ps1")

function Assert-ArtifactHash {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Path,
        [Parameter(Mandatory = $true)]
        [string]$ExpectedSha256
    )

    $actual = (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($actual -cne $ExpectedSha256) {
        throw "downloaded artifact hash mismatch for $Path`: expected $ExpectedSha256, found $actual"
    }
}

function Set-DeterministicDirectUrlMetadata {
    param(
        [Parameter(Mandatory = $true)]
        [string]$RuntimeRoot,
        [Parameter(Mandatory = $true)]
        [object]$Artifact
    )

    $distInfo = Join-Path $RuntimeRoot ([string]$Artifact.DistInfo)
    $directUrlPath = Join-Path $distInfo "direct_url.json"
    $recordPath = Join-Path $distInfo "RECORD"
    if (-not (Test-Path -LiteralPath $directUrlPath -PathType Leaf) -or
        -not (Test-Path -LiteralPath $recordPath -PathType Leaf)) {
        throw "installed wheel metadata is incomplete for $($Artifact.Name)"
    }
    $metadata = [ordered]@{
        archive_info = [ordered]@{
            hash = "sha256=$($Artifact.Sha256)"
            hashes = [ordered]@{ sha256 = [string]$Artifact.Sha256 }
        }
        url = [string]$Artifact.Url
    }
    $json = $metadata | ConvertTo-Json -Compress -Depth 4
    $utf8 = [System.Text.UTF8Encoding]::new($false)
    [System.IO.File]::WriteAllText($directUrlPath, $json, $utf8)

    $bytes = [System.IO.File]::ReadAllBytes($directUrlPath)
    $sha256 = [System.Security.Cryptography.SHA256]::Create()
    try {
        $encodedHash = [Convert]::ToBase64String($sha256.ComputeHash($bytes)).TrimEnd("=")
    } finally {
        $sha256.Dispose()
    }
    $encodedHash = $encodedHash.Replace("+", "-").Replace("/", "_")
    $relativeDirectUrl = "$($Artifact.DistInfo)/direct_url.json"
    $updated = $false
    $recordLines = foreach ($line in [System.IO.File]::ReadAllLines($recordPath)) {
        if ($line.StartsWith("$relativeDirectUrl,", [System.StringComparison]::Ordinal)) {
            $updated = $true
            "$relativeDirectUrl,sha256=$encodedHash,$($bytes.Length)"
        } else {
            $line
        }
    }
    if (-not $updated) {
        throw "installed wheel RECORD omits $relativeDirectUrl"
    }
    [System.IO.File]::WriteAllLines($recordPath, $recordLines, $utf8)
}

function Remove-UnusedWheelLaunchers {
    param(
        [Parameter(Mandatory = $true)]
        [string]$RuntimeRoot,
        [Parameter(Mandatory = $true)]
        [object]$Artifact
    )

    $launchers = @($Artifact.Launchers)
    if ($launchers.Count -eq 0) {
        return
    }
    $launcherRoot = Join-Path $RuntimeRoot "bin"
    $actualLaunchers = @(
        Get-ChildItem -LiteralPath $launcherRoot -File |
            Select-Object -ExpandProperty Name |
            Sort-Object
    )
    $expectedLaunchers = @($launchers | Sort-Object)
    if (Compare-Object -ReferenceObject $expectedLaunchers -DifferenceObject $actualLaunchers) {
        throw "installed wheel launchers do not match the pinned $($Artifact.Name) metadata"
    }

    $distInfo = Join-Path $RuntimeRoot ([string]$Artifact.DistInfo)
    $recordPath = Join-Path $distInfo "RECORD"
    $launcherRecords = @($launchers | ForEach-Object { "../../bin/$_" })
    $removed = 0
    $recordLines = foreach ($line in [System.IO.File]::ReadAllLines($recordPath)) {
        $relative = $line.Split(",", 2)[0]
        if ($launcherRecords -ccontains $relative) {
            $removed += 1
        } else {
            $line
        }
    }
    if ($removed -ne $launcherRecords.Count) {
        throw "installed wheel RECORD does not bind every removable launcher for $($Artifact.Name)"
    }
    $utf8 = [System.Text.UTF8Encoding]::new($false)
    [System.IO.File]::WriteAllLines($recordPath, $recordLines, $utf8)
    Remove-Item -LiteralPath $launcherRoot -Recurse -Force
}

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$packageInputs = Get-MaledictusPackageInputs `
    -ProjectRoot $repositoryRoot `
    -NaginiSource $NaginiSource
$initialPackageInputSnapshot = Get-MaledictusPackageInputSnapshot -Inputs $packageInputs

$buildArguments = @("build")
if ($Profile -eq "release") {
    $buildArguments += "--release"
}
& $CargoPath @buildArguments
if ($LASTEXITCODE -ne 0) {
    throw "cargo build failed with exit code $LASTEXITCODE"
}

$metadata = (& $CargoPath metadata --no-deps --format-version 1 | ConvertFrom-Json)
if ($LASTEXITCODE -ne 0) {
    throw "cargo metadata failed with exit code $LASTEXITCODE"
}
$profileDirectory = Join-Path $metadata.target_directory $Profile
$executable = Join-Path $profileDirectory "maledictus.exe"
if (-not (Test-Path -LiteralPath $executable -PathType Leaf)) {
    throw "built executable not found at $executable"
}

$z3Candidates = Get-ChildItem -LiteralPath (Join-Path $profileDirectory "build") -Directory -Filter "z3-sys-*" |
    ForEach-Object {
        Get-ChildItem -LiteralPath (Join-Path $_.FullName "out") -Directory -Filter "z3-*" -ErrorAction SilentlyContinue
    } |
    ForEach-Object {
        Get-Item -LiteralPath (Join-Path $_.FullName "bin/libz3.dll") -ErrorAction SilentlyContinue
    } |
    Sort-Object LastWriteTimeUtc -Descending
$z3Runtime = $z3Candidates | Select-Object -First 1
if ($null -eq $z3Runtime) {
    throw "the pinned Z3 runtime DLL was not found below $profileDirectory/build"
}

New-Item -ItemType Directory -Path $Destination -Force | Out-Null
$packagedExecutable = Join-Path $Destination "maledictus.exe"
$packagedZ3 = Join-Path $Destination "libz3.dll"
Copy-Item -LiteralPath $executable -Destination $packagedExecutable -Force
Copy-Item -LiteralPath $z3Runtime.FullName -Destination $packagedZ3 -Force

$pythonRuntime = Join-Path $Destination "python-typecheck"
$destinationFullPath = [System.IO.Path]::GetFullPath($Destination).TrimEnd("\") + "\"
$pythonRuntimeFullPath = [System.IO.Path]::GetFullPath($pythonRuntime)
if (-not $pythonRuntimeFullPath.StartsWith($destinationFullPath, [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "refusing to replace Python typechecker outside package destination: $pythonRuntimeFullPath"
}
if (Test-Path -LiteralPath $pythonRuntimeFullPath) {
    Remove-Item -LiteralPath $pythonRuntimeFullPath -Recurse -Force
}
New-Item -ItemType Directory -Path $pythonRuntimeFullPath -Force | Out-Null

$temporaryRoot = Join-Path ([System.IO.Path]::GetTempPath()) ("maledictus-python-" + [guid]::NewGuid().ToString("N"))
New-Item -ItemType Directory -Path $temporaryRoot -Force | Out-Null
try {
    $embeddedArchive = Join-Path $temporaryRoot "python-embed.zip"
    $embeddedUrl = "https://www.python.org/ftp/python/$PythonVersion/python-$PythonVersion-embed-amd64.zip"
    Invoke-WebRequest -Uri $embeddedUrl -OutFile $embeddedArchive
    Assert-ArtifactHash `
        -Path $embeddedArchive `
        -ExpectedSha256 "4acbed6dd1c744b0376e3b1cf57ce906f9dc9e95e68824584c8099a63025a3c3"
    Expand-Archive -LiteralPath $embeddedArchive -DestinationPath $pythonRuntimeFullPath

    $pathConfiguration = Get-ChildItem -LiteralPath $pythonRuntimeFullPath -File -Filter "python*._pth"
    if (@($pathConfiguration).Count -ne 1) {
        throw "embedded Python payload must contain exactly one python*._pth file"
    }
    $configuredPathLines = foreach ($line in Get-Content -LiteralPath $pathConfiguration.FullName) {
        if ($line -ceq "#import site") { "import site" } else { $line }
    }
    $configuredPathLines | Set-Content -LiteralPath $pathConfiguration.FullName -Encoding ascii

    $wheelArtifacts = @(
        [ordered]@{
            Name = "mypy-1.5.0-py3-none-any.whl"
            DistInfo = "mypy-1.5.0.dist-info"
            Launchers = @("dmypy.exe", "mypy.exe", "mypyc.exe", "stubgen.exe", "stubtest.exe")
            Url = "https://files.pythonhosted.org/packages/d9/ff/b724e59d57d4442617a284a0f0e134767969108117df040c0b54ba80ef89/mypy-1.5.0-py3-none-any.whl"
            Sha256 = "69b32d0dedd211b80f1b7435644e1ef83033a2af2ac65adcdc87c38db68a86be"
        },
        [ordered]@{
            Name = "mypy_extensions-1.1.0-py3-none-any.whl"
            DistInfo = "mypy_extensions-1.1.0.dist-info"
            Launchers = @()
            Url = "https://files.pythonhosted.org/packages/79/7b/2c79738432f5c924bef5071f933bcc9efd0473bac3b4aa584a6f7c1c8df8/mypy_extensions-1.1.0-py3-none-any.whl"
            Sha256 = "1be4cccdb0f2482337c4743e60421de3a356cd97508abadd57d47403e94f5505"
        },
        [ordered]@{
            Name = "typing_extensions-4.12.2-py3-none-any.whl"
            DistInfo = "typing_extensions-4.12.2.dist-info"
            Launchers = @()
            Url = "https://files.pythonhosted.org/packages/26/9f/ad63fc0248c5379346306f8668cda6e2e2e9c95e01216d2b8ffd9ff037d0/typing_extensions-4.12.2-py3-none-any.whl"
            Sha256 = "04e5ca0351e0f3f85c6853954072df659d0d13fac324d0072316b67d7794700d"
        }
    )
    $wheelPaths = foreach ($artifact in $wheelArtifacts) {
        $wheelPath = Join-Path $temporaryRoot $artifact.Name
        Invoke-WebRequest -Uri $artifact.Url -OutFile $wheelPath
        Assert-ArtifactHash -Path $wheelPath -ExpectedSha256 $artifact.Sha256
        $wheelPath
    }

    & $PythonPath -m pip install `
        --disable-pip-version-check `
        --no-compile `
        --no-deps `
        --no-index `
        --target $pythonRuntimeFullPath `
        @wheelPaths
    if ($LASTEXITCODE -ne 0) {
        throw "installing the pinned mypy runtime failed with exit code $LASTEXITCODE"
    }
    foreach ($artifact in $wheelArtifacts) {
        Remove-UnusedWheelLaunchers -RuntimeRoot $pythonRuntimeFullPath -Artifact $artifact
        Set-DeterministicDirectUrlMetadata -RuntimeRoot $pythonRuntimeFullPath -Artifact $artifact
    }
} finally {
    if (Test-Path -LiteralPath $temporaryRoot) {
        Remove-Item -LiteralPath $temporaryRoot -Recurse -Force
    }
}

$naginiContracts = Join-Path $NaginiSource "nagini_contracts"
if (-not (Test-Path -LiteralPath (Join-Path $naginiContracts "contracts.py") -PathType Leaf)) {
    throw "Nagini contract support was not found below $NaginiSource"
}
$pythonSupport = Join-Path $pythonRuntimeFullPath "support"
New-Item -ItemType Directory -Path $pythonSupport -Force | Out-Null
Get-ChildItem -LiteralPath "python_typecheck/support" -Force | ForEach-Object {
    Copy-Item -LiteralPath $_.FullName -Destination $pythonSupport -Recurse -Force
}
Copy-Item -LiteralPath $naginiContracts -Destination $pythonSupport -Recurse -Force
Copy-Item -LiteralPath "python_typecheck/mypy-1.5.ini" -Destination $pythonRuntimeFullPath -Force

$packagedPython = Join-Path $pythonRuntimeFullPath "python.exe"
& $packagedPython -B -c "import mypy.version; assert mypy.version.__version__ == '1.5.0'"
if ($LASTEXITCODE -ne 0) {
    throw "the self-contained pinned mypy runtime failed its import check"
}

$typescriptRuntime = Join-Path $Destination "typescript"
$typescriptCompiler = Join-Path $typescriptRuntime "compiler"
$compilerFullPath = [System.IO.Path]::GetFullPath($typescriptCompiler)
if (-not $compilerFullPath.StartsWith($destinationFullPath, [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "refusing to replace TypeScript compiler outside package destination: $compilerFullPath"
}
if (Test-Path -LiteralPath $compilerFullPath) {
    Remove-Item -LiteralPath $compilerFullPath -Recurse -Force
}
New-Item -ItemType Directory -Path $typescriptCompiler -Force | Out-Null
Copy-Item -LiteralPath "typescript/frontend.cjs" -Destination (Join-Path $typescriptRuntime "frontend.cjs") -Force
Copy-Item -Path "node_modules/typescript/*" -Destination $typescriptCompiler -Recurse -Force

Assert-MaledictusPackageInputsUnchanged `
    -Inputs $packageInputs `
    -ExpectedSnapshot $initialPackageInputSnapshot

$capabilitiesJson = (& $packagedExecutable capabilities | Out-String).Trim()
if ($LASTEXITCODE -ne 0) {
    throw "packaged verifier capability discovery failed with exit code $LASTEXITCODE"
}
$capabilities = $capabilitiesJson | ConvertFrom-Json -ErrorAction Stop
if ($capabilities.schema -cne "maledictus-capabilities/v1" -or
    $capabilities.verifier -cne "maledictus") {
    throw "packaged verifier returned unexpected capabilities"
}
[System.IO.File]::WriteAllText(
    (Join-Path $Destination "capabilities.json"),
    "$capabilitiesJson`n",
    [System.Text.UTF8Encoding]::new($false)
)

$destinationRoot = (Resolve-Path -LiteralPath $Destination).Path.TrimEnd("\") + "\"
$manifest = [ordered]@{
    schema = "maledictus-windows-package/v2"
    profile = $Profile
    source_input_sha256 = $initialPackageInputSnapshot
    files = @(
        Get-ChildItem -LiteralPath $Destination -File -Recurse |
            Where-Object { $_.Name -ne "package-manifest.json" } |
            Sort-Object FullName |
            ForEach-Object {
                [ordered]@{
                    path = $_.FullName.Substring($destinationRoot.Length).Replace("\", "/")
                    sha256 = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash.ToLowerInvariant()
                }
            }
    )
}
$manifestPath = Join-Path $Destination "package-manifest.json"
$manifest | ConvertTo-Json -Depth 4 | Set-Content -LiteralPath $manifestPath -Encoding utf8
Assert-MaledictusPackageInputsUnchanged `
    -Inputs $packageInputs `
    -ExpectedSnapshot $initialPackageInputSnapshot
Write-Output "packaged Maledictus, Z3, pinned mypy, Nagini contracts, and the TypeScript frontend at $Destination"
