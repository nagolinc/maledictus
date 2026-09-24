param(
    [string]$Destination = ".cache/release/windows-x86_64",
    [string]$ExamplesRoot = "examples",
    [string]$NaginiSource = ".upstream/nagini/src"
)

$ErrorActionPreference = "Stop"

. (Join-Path $PSScriptRoot "package-input-snapshot.ps1")

function Get-ManifestBundleHash {
    param(
        [Parameter(Mandatory = $true)]
        [object[]]$Entries,
        [Parameter(Mandatory = $true)]
        [string]$Prefix
    )

    $hashesByPath = @{}
    $relativePaths = [System.Collections.Generic.List[string]]::new()
    foreach ($entry in $Entries) {
        $path = [string]$entry.path
        if (-not $path.StartsWith($Prefix, [System.StringComparison]::Ordinal)) {
            continue
        }
        $relative = $path.Substring($Prefix.Length)
        if ($relative.IndexOf("/__pycache__/", [System.StringComparison]::Ordinal) -ge 0 -or
            $relative.EndsWith(".pyc", [System.StringComparison]::Ordinal) -or
            $relative.EndsWith(".pyo", [System.StringComparison]::Ordinal)) {
            continue
        }
        $relativePaths.Add($relative)
        $hashesByPath[$relative] = [string]$entry.sha256
    }
    $paths = $relativePaths.ToArray()
    [Array]::Sort($paths, [System.StringComparer]::Ordinal)
    $stream = [System.IO.MemoryStream]::new()
    try {
        foreach ($relative in $paths) {
            $pathBytes = [System.Text.Encoding]::UTF8.GetBytes($relative)
            $hashText = $hashesByPath[$relative]
            $hashBytes = [byte[]]::new(32)
            for ($index = 0; $index -lt $hashBytes.Length; $index += 1) {
                $hashBytes[$index] = [Convert]::ToByte($hashText.Substring($index * 2, 2), 16)
            }
            foreach ($field in @($pathBytes, $hashBytes)) {
                $lengthBytes = [BitConverter]::GetBytes([uint64]$field.Length)
                if ([BitConverter]::IsLittleEndian) {
                    [Array]::Reverse($lengthBytes)
                }
                $stream.Write($lengthBytes, 0, $lengthBytes.Length)
                $stream.Write($field, 0, $field.Length)
            }
        }
        $sha256 = [System.Security.Cryptography.SHA256]::Create()
        try {
            return ([BitConverter]::ToString($sha256.ComputeHash($stream.ToArray()))).Replace("-", "").ToLowerInvariant()
        } finally {
            $sha256.Dispose()
        }
    } finally {
        $stream.Dispose()
    }
}

function Get-ManifestContentBundleHash {
    param(
        [Parameter(Mandatory = $true)]
        [object[]]$Entries,
        [Parameter(Mandatory = $true)]
        [string]$Prefix,
        [Parameter(Mandatory = $true)]
        [string]$Root
    )

    $paths = @(
        $Entries |
            ForEach-Object { [string]$_.path } |
            Where-Object { $_.StartsWith($Prefix, [System.StringComparison]::Ordinal) } |
            ForEach-Object { $_.Substring($Prefix.Length) }
    )
    [Array]::Sort($paths, [System.StringComparer]::Ordinal)
    $stream = [System.IO.MemoryStream]::new()
    try {
        foreach ($relative in $paths) {
            $pathBytes = [System.Text.Encoding]::UTF8.GetBytes($relative)
            $content = [System.IO.File]::ReadAllBytes(
                (Join-Path $Root ($Prefix + $relative).Replace("/", "\"))
            )
            foreach ($field in @($pathBytes, $content)) {
                $lengthBytes = [BitConverter]::GetBytes([uint64]$field.Length)
                if ([BitConverter]::IsLittleEndian) {
                    [Array]::Reverse($lengthBytes)
                }
                $stream.Write($lengthBytes, 0, $lengthBytes.Length)
                $stream.Write($field, 0, $field.Length)
            }
        }
        $sha256 = [System.Security.Cryptography.SHA256]::Create()
        try {
            return ([BitConverter]::ToString($sha256.ComputeHash($stream.ToArray()))).Replace("-", "").ToLowerInvariant()
        } finally {
            $sha256.Dispose()
        }
    } finally {
        $stream.Dispose()
    }
}

function Assert-DeterministicDirectUrlMetadata {
    param(
        [Parameter(Mandatory = $true)]
        [string]$RuntimeRoot,
        [Parameter(Mandatory = $true)]
        [string]$DistInfo,
        [Parameter(Mandatory = $true)]
        [string]$ExpectedUrl,
        [Parameter(Mandatory = $true)]
        [string]$ExpectedSha256
    )

    $directUrlPath = Join-Path $RuntimeRoot "$DistInfo/direct_url.json"
    $recordPath = Join-Path $RuntimeRoot "$DistInfo/RECORD"
    $metadata = Get-Content -LiteralPath $directUrlPath -Raw | ConvertFrom-Json
    if ($metadata.url -cne $ExpectedUrl -or
        $metadata.archive_info.hash -cne "sha256=$ExpectedSha256" -or
        $metadata.archive_info.hashes.sha256 -cne $ExpectedSha256) {
        throw "installed wheel provenance is not deterministic and pinned for $DistInfo"
    }

    $bytes = [System.IO.File]::ReadAllBytes($directUrlPath)
    $sha256 = [System.Security.Cryptography.SHA256]::Create()
    try {
        $encodedHash = [Convert]::ToBase64String($sha256.ComputeHash($bytes)).TrimEnd("=")
    } finally {
        $sha256.Dispose()
    }
    $encodedHash = $encodedHash.Replace("+", "-").Replace("/", "_")
    $relativeDirectUrl = "$DistInfo/direct_url.json"
    $expectedRecord = "$relativeDirectUrl,sha256=$encodedHash,$($bytes.Length)"
    $recordMatches = @(
        [System.IO.File]::ReadAllLines($recordPath) |
            Where-Object { $_.StartsWith("$relativeDirectUrl,", [System.StringComparison]::Ordinal) }
    )
    if ($recordMatches.Count -ne 1 -or $recordMatches[0] -cne $expectedRecord) {
        throw "installed wheel RECORD does not bind deterministic provenance for $DistInfo"
    }
}

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
$repositoryPrefix = $repositoryRoot.TrimEnd("\") + "\"
$destinationInput = if ([System.IO.Path]::IsPathRooted($Destination)) {
    $Destination
} else {
    Join-Path $repositoryRoot $Destination
}
$examplesInput = if ([System.IO.Path]::IsPathRooted($ExamplesRoot)) {
    $ExamplesRoot
} else {
    Join-Path $repositoryRoot $ExamplesRoot
}
$destinationPath = (Resolve-Path -LiteralPath $destinationInput).Path
$examplesPath = (Resolve-Path -LiteralPath $examplesInput).Path
if (-not $examplesPath.StartsWith($repositoryPrefix, [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "example request directory escapes the repository: $examplesPath"
}
$destinationPrefix = $destinationPath.TrimEnd("\") + "\"
$manifestPath = Join-Path $destinationPath "package-manifest.json"
if (-not (Test-Path -LiteralPath $manifestPath -PathType Leaf)) {
    throw "Windows package manifest not found at $manifestPath"
}

$manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
if ($manifest.schema -ne "maledictus-windows-package/v2") {
    throw "unexpected Windows package manifest schema: $($manifest.schema)"
}
if ($manifest.profile -ne "release") {
    throw "Windows package smoke verification requires a release package"
}
$packageInputs = Get-MaledictusPackageInputs `
    -ProjectRoot $repositoryRoot `
    -NaginiSource $NaginiSource
$sourceInputSnapshot = Get-MaledictusPackageInputSnapshot -Inputs $packageInputs
if ($manifest.source_input_sha256 -cne $sourceInputSnapshot) {
    throw (
        "Windows package source-input snapshot does not match the current tree: " +
        "manifest=$($manifest.source_input_sha256), current=$sourceInputSnapshot"
    )
}

$entries = @($manifest.files)
if ($entries.Count -eq 0) {
    throw "Windows package manifest contains no payload files"
}
$manifestPaths = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
$manifestHashes = @{}
foreach ($entry in $entries) {
    $relativePath = [string]$entry.path
    $declaredHash = [string]$entry.sha256
    if ([string]::IsNullOrWhiteSpace($relativePath) -or
        $relativePath.Contains("\") -or
        [System.IO.Path]::IsPathRooted($relativePath) -or
        @($relativePath.Split("/") | Where-Object { $_ -in @("", ".", "..") }).Count -ne 0) {
        throw "unsafe package manifest path: $relativePath"
    }
    if ($relativePath -notin @("maledictus.exe", "libz3.dll", "capabilities.json", "typescript/frontend.cjs") -and
        -not $relativePath.StartsWith("python-typecheck/", [System.StringComparison]::Ordinal) -and
        -not $relativePath.StartsWith("typescript/compiler/", [System.StringComparison]::Ordinal)) {
        throw "unexpected file in Windows package manifest: $relativePath"
    }
    if (-not $manifestPaths.Add($relativePath)) {
        throw "duplicate package manifest path: $relativePath"
    }
    if ($declaredHash -cnotmatch "^[0-9a-f]{64}$") {
        throw "invalid SHA-256 for package manifest path $relativePath"
    }
    $candidate = [System.IO.Path]::GetFullPath(
        (Join-Path $destinationPath $relativePath.Replace("/", "\"))
    )
    if (-not $candidate.StartsWith($destinationPrefix, [System.StringComparison]::OrdinalIgnoreCase)) {
        throw "package manifest path escapes the destination: $relativePath"
    }
    if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) {
        throw "package manifest file is missing: $relativePath"
    }
    $actualHash = (Get-FileHash -LiteralPath $candidate -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($actualHash -cne $declaredHash) {
        throw "package hash mismatch for ${relativePath}: expected $declaredHash, found $actualHash"
    }
    $manifestHashes[$relativePath] = $declaredHash
}

foreach ($requiredPath in @(
    "maledictus.exe",
    "libz3.dll",
    "capabilities.json",
    "python-typecheck/python.exe",
    "python-typecheck/python312.zip",
    "python-typecheck/mypy-1.5.ini",
    "python-typecheck/mypy/version.py",
    "python-typecheck/mypy-1.5.0.dist-info/METADATA",
    "python-typecheck/mypy_extensions.py",
    "python-typecheck/typing_extensions.py",
    "python-typecheck/support/dagcert/runtime.pyi",
    "python-typecheck/support/nagini_contracts/contracts.py",
    "typescript/frontend.cjs",
    "typescript/compiler/package.json"
)) {
    if (-not $manifestPaths.Contains($requiredPath)) {
        throw "Windows package manifest omits required payload: $requiredPath"
    }
}

$pythonRuntimePath = Join-Path $destinationPath "python-typecheck"
Assert-DeterministicDirectUrlMetadata `
    -RuntimeRoot $pythonRuntimePath `
    -DistInfo "mypy-1.5.0.dist-info" `
    -ExpectedUrl "https://files.pythonhosted.org/packages/d9/ff/b724e59d57d4442617a284a0f0e134767969108117df040c0b54ba80ef89/mypy-1.5.0-py3-none-any.whl" `
    -ExpectedSha256 "69b32d0dedd211b80f1b7435644e1ef83033a2af2ac65adcdc87c38db68a86be"
Assert-DeterministicDirectUrlMetadata `
    -RuntimeRoot $pythonRuntimePath `
    -DistInfo "mypy_extensions-1.1.0.dist-info" `
    -ExpectedUrl "https://files.pythonhosted.org/packages/79/7b/2c79738432f5c924bef5071f933bcc9efd0473bac3b4aa584a6f7c1c8df8/mypy_extensions-1.1.0-py3-none-any.whl" `
    -ExpectedSha256 "1be4cccdb0f2482337c4743e60421de3a356cd97508abadd57d47403e94f5505"
Assert-DeterministicDirectUrlMetadata `
    -RuntimeRoot $pythonRuntimePath `
    -DistInfo "typing_extensions-4.12.2.dist-info" `
    -ExpectedUrl "https://files.pythonhosted.org/packages/26/9f/ad63fc0248c5379346306f8668cda6e2e2e9c95e01216d2b8ffd9ff037d0/typing_extensions-4.12.2-py3-none-any.whl" `
    -ExpectedSha256 "04e5ca0351e0f3f85c6853954072df659d0d13fac324d0072316b67d7794700d"
if (Test-Path -LiteralPath (Join-Path $pythonRuntimePath "bin")) {
    throw "packaged typechecker retained host-path-dependent console launchers"
}
$mypyRecord = Join-Path $pythonRuntimePath "mypy-1.5.0.dist-info/RECORD"
if ([System.IO.File]::ReadAllLines($mypyRecord) | Where-Object { $_.StartsWith("../../bin/", [System.StringComparison]::Ordinal) }) {
    throw "packaged mypy RECORD retained removed console-launcher entries"
}

$actualPaths = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
Get-ChildItem -LiteralPath $destinationPath -File -Recurse |
    Where-Object { $_.FullName -cne $manifestPath } |
    ForEach-Object {
        $relativePath = $_.FullName.Substring($destinationPrefix.Length).Replace("\", "/")
        if (-not $actualPaths.Add($relativePath)) {
            throw "duplicate physical package path: $relativePath"
        }
    }
if ($actualPaths.Count -ne $manifestPaths.Count) {
    throw "package contents and manifest differ in size: $($actualPaths.Count) files vs $($manifestPaths.Count) entries"
}
foreach ($relativePath in $actualPaths) {
    if (-not $manifestPaths.Contains($relativePath)) {
        throw "unmanifested file in Windows package: $relativePath"
    }
}
$pythonRuntimeBundleHash = Get-ManifestBundleHash -Entries $entries -Prefix "python-typecheck/"
$typescriptCompilerBundleHash = Get-ManifestContentBundleHash `
    -Entries $entries `
    -Prefix "typescript/compiler/" `
    -Root $destinationPath

$executable = Join-Path $destinationPath "maledictus.exe"
$packagedCapabilities = (Get-Content -LiteralPath (Join-Path $destinationPath "capabilities.json") -Raw).Trim()
$capabilities = $packagedCapabilities | ConvertFrom-Json -ErrorAction Stop
if ($capabilities.schema -cne "maledictus-capabilities/v1" -or
    $capabilities.verifier -cne "maledictus") {
    throw "packaged verifier capabilities have an unexpected schema or verifier"
}
$actualCapabilities = (& $executable capabilities | Out-String).Trim()
if ($LASTEXITCODE -ne 0 -or $actualCapabilities -cne $packagedCapabilities) {
    throw "packaged capabilities do not match the executable"
}
$requests = @(Get-ChildItem -LiteralPath $examplesPath -File -Filter "*.request.json" | Sort-Object Name)
if ($requests.Count -eq 0) {
    throw "no checked-in example requests found below $ExamplesRoot"
}
$proved = 0
foreach ($requestFile in $requests) {
    $request = Get-Content -LiteralPath $requestFile.FullName -Raw | ConvertFrom-Json
    $requestRootInput = if ([System.IO.Path]::IsPathRooted([string]$request.source_root)) {
        [string]$request.source_root
    } else {
        Join-Path $repositoryRoot ([string]$request.source_root)
    }
    $requestRoot = (Resolve-Path -LiteralPath $requestRootInput).Path
    $requestRootPrefix = $requestRoot.TrimEnd("\") + "\"
    if ($requestRoot -cne $repositoryRoot -and
        -not $requestRoot.StartsWith($repositoryPrefix, [System.StringComparison]::OrdinalIgnoreCase)) {
        throw "example source root escapes the repository in $($requestFile.Name)"
    }
    Push-Location $repositoryRoot
    try {
        $rawResponse = & $executable verify --request $requestFile.FullName
        $exitCode = $LASTEXITCODE
    } finally {
        Pop-Location
    }
    if ($exitCode -ne 0) {
        throw "packaged verifier failed $($requestFile.Name) with exit code $exitCode"
    }
    $response = $rawResponse | Out-String | ConvertFrom-Json
    if ($response.schema -ne "maledictus-verification-result/v7" -or $response.status -ne "proved") {
        throw "packaged verifier did not prove $($requestFile.Name): schema=$($response.schema), status=$($response.status)"
    }
    if ($response.proof_obligation -ne $request.proof_obligation -or
        $response.source_fingerprint -ne $request.source_fingerprint) {
        throw "packaged verifier response identity does not match $($requestFile.Name)"
    }
    if (@($response.diagnostics).Count -ne 0) {
        throw "packaged verifier emitted diagnostics for $($requestFile.Name)"
    }
    $requestedFiles = @($request.files)
    $resultFiles = @($response.files)
    if ($resultFiles.Count -ne $requestedFiles.Count -or
        @($resultFiles | Where-Object { $_.result -ne "proved" }).Count -ne 0) {
        throw "packaged verifier did not prove every requested file in $($requestFile.Name)"
    }
    foreach ($requestedFile in $requestedFiles) {
        $matches = @($resultFiles | Where-Object { $_.path -ceq $requestedFile.path })
        if ($matches.Count -ne 1) {
            throw "packaged verifier response does not bind requested path $($requestedFile.path) exactly once"
        }
        $sourcePath = [System.IO.Path]::GetFullPath(
            (Join-Path $requestRoot ([string]$requestedFile.path))
        )
        if (-not $sourcePath.StartsWith($requestRootPrefix, [System.StringComparison]::OrdinalIgnoreCase)) {
            throw "requested example source path escapes its source root: $($requestedFile.path)"
        }
        $sourceHash = (Get-FileHash -LiteralPath $sourcePath -Algorithm SHA256).Hash.ToLowerInvariant()
        if ($matches[0].sha256 -cne $sourceHash) {
            throw "packaged verifier returned the wrong source hash for $($requestedFile.path)"
        }
    }
    if ($response.verifier_identity.executable_sha256 -cne $manifestHashes["maledictus.exe"]) {
        throw "packaged verifier executable identity does not match the manifest"
    }
    foreach ($identityHash in @(
        [string]$response.verifier_identity.frontend_bundle_sha256,
        [string]$response.verifier_identity.kernel_bundle_sha256
    )) {
        if ($identityHash -cnotmatch "^[0-9a-f]{64}$") {
            throw "packaged verifier omitted a valid source-bundle identity"
        }
    }
    $pythonFiles = @($requestedFiles | Where-Object { $_.language -ceq "python" })
    if ($pythonFiles.Count -ne 0) {
        if ($response.python_typechecker.checker -cne "mypy" -or
            $response.python_typechecker.checker_version -cne "1.5.0" -or
            $response.python_typechecker.profile -cne "strict-issuance") {
            throw "packaged verifier omitted the exact strict mypy identity for $($requestFile.Name)"
        }
        if ($response.python_typechecker.runtime_executable_sha256 -cne $manifestHashes["python-typecheck/python.exe"]) {
            throw "packaged verifier did not execute the packaged Python runtime for $($requestFile.Name)"
        }
        if ($response.python_typechecker.runtime_bundle_sha256 -cne $pythonRuntimeBundleHash) {
            throw "packaged verifier Python runtime bundle identity does not match the package manifest"
        }
        foreach ($identityHash in @(
            [string]$response.python_typechecker.package_sha256,
            [string]$response.python_typechecker.configuration_sha256,
            [string]$response.python_typechecker.contract_support_sha256
        )) {
            if ($identityHash -cnotmatch "^[0-9a-f]{64}$") {
                throw "packaged verifier omitted a valid Python typechecker dependency identity"
            }
        }
    }
    $typescriptFiles = @(
        $requestedFiles | Where-Object { $_.language -in @("javascript", "typescript") }
    )
    if ($typescriptFiles.Count -ne 0) {
        if ($response.typescript_toolchain.compiler -cne "typescript" -or
            $response.typescript_toolchain.compiler_version -cne "5.9.3" -or
            $response.typescript_toolchain.compiler_bundle_sha256 -cne $typescriptCompilerBundleHash -or
            $response.typescript_toolchain.runtime -cne "node") {
            throw "packaged verifier omitted the exact TypeScript toolchain identity for $($requestFile.Name)"
        }
        $nodePath = if (-not [string]::IsNullOrWhiteSpace($env:MALEDICTUS_NODE)) {
            (Resolve-Path -LiteralPath $env:MALEDICTUS_NODE -ErrorAction Stop).Path
        } else {
            (Get-Command node -CommandType Application -ErrorAction Stop).Source
        }
        if (-not (Test-Path -LiteralPath $nodePath -PathType Leaf)) {
            throw "packaged TypeScript verification selected a missing Node executable"
        }
        $nodeHash = (Get-FileHash -LiteralPath $nodePath -Algorithm SHA256).Hash.ToLowerInvariant()
        $nodeVersion = (& $nodePath --version | Out-String).Trim()
        if ($LASTEXITCODE -ne 0 -or
            $response.typescript_toolchain.runtime_version -cne $nodeVersion -or
            $response.typescript_toolchain.runtime_executable_sha256 -cne $nodeHash) {
            throw "packaged verifier TypeScript runtime identity does not match executed Node"
        }
    }
    $requestedMixedProperty = $request.PSObject.Properties["cross_language_bindings"]
    $requestedMixedBindings = @(
        if ($null -ne $requestedMixedProperty) {
            $requestedMixedProperty.Value
        }
    )
    $resultMixedBindings = @($response.cross_language_bindings)
    if ($resultMixedBindings.Count -ne $requestedMixedBindings.Count) {
        throw "packaged verifier returned the wrong mixed-language binding count for $($requestFile.Name)"
    }
    foreach ($requestedBinding in $requestedMixedBindings) {
        $matches = @($resultMixedBindings | Where-Object { $_.id -ceq $requestedBinding.id })
        if ($matches.Count -ne 1) {
            throw "packaged verifier did not bind mixed-language id $($requestedBinding.id) exactly once"
        }
        $resultBinding = $matches[0]
        foreach ($field in @(
            "caller_path",
            "python_module",
            "python_symbol",
            "provider_path",
            "provider_export",
            "return_type"
        )) {
            if ([string]$resultBinding.$field -cne [string]$requestedBinding.$field) {
                throw "packaged verifier mixed-language field $field does not match the request"
            }
        }
        if ((@($resultBinding.parameters) | ConvertTo-Json -Compress) -cne
            (@($requestedBinding.parameters) | ConvertTo-Json -Compress)) {
            throw "packaged verifier mixed-language parameter signature does not match the request"
        }
        $callerFile = @($resultFiles | Where-Object { $_.path -ceq $requestedBinding.caller_path })
        $providerFile = @($resultFiles | Where-Object { $_.path -ceq $requestedBinding.provider_path })
        if ($callerFile.Count -ne 1 -or $providerFile.Count -ne 1 -or
            $resultBinding.caller_sha256 -cne $callerFile[0].sha256 -or
            $resultBinding.provider_sha256 -cne $providerFile[0].sha256 -or
            [string]$resultBinding.interface_sha256 -cnotmatch "^[0-9a-f]{64}$") {
            throw "packaged verifier mixed-language source/interface identity is incomplete"
        }
    }
    $proved += 1
}

Write-Output "verified $($manifestPaths.Count) packaged payload files and proved $proved example requests"
