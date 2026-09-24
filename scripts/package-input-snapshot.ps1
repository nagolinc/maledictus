Set-StrictMode -Version Latest

function Get-MaledictusPackageInputs {
    param(
        [Parameter(Mandatory = $true)]
        [string]$ProjectRoot,
        [Parameter(Mandatory = $true)]
        [string]$NaginiSource
    )

    $root = [System.IO.Path]::GetFullPath($ProjectRoot)
    $naginiRoot = if ([System.IO.Path]::IsPathRooted($NaginiSource)) {
        [System.IO.Path]::GetFullPath($NaginiSource)
    } else {
        [System.IO.Path]::GetFullPath((Join-Path $root $NaginiSource))
    }
    return @(
        [pscustomobject]@{ Label = "Cargo.toml"; Path = (Join-Path $root "Cargo.toml"); Required = $true },
        [pscustomobject]@{ Label = "Cargo.lock"; Path = (Join-Path $root "Cargo.lock"); Required = $true },
        [pscustomobject]@{ Label = "rust-toolchain.toml"; Path = (Join-Path $root "rust-toolchain.toml"); Required = $true },
        [pscustomobject]@{ Label = "build.rs"; Path = (Join-Path $root "build.rs"); Required = $false },
        [pscustomobject]@{ Label = ".cargo"; Path = (Join-Path $root ".cargo"); Required = $false },
        [pscustomobject]@{ Label = "src"; Path = (Join-Path $root "src"); Required = $true },
        [pscustomobject]@{ Label = "formal/extraction/call-binding-full/extraction.json"; Path = (Join-Path $root "formal/extraction/call-binding-full/extraction.json"); Required = $true },
        [pscustomobject]@{ Label = "package-lock.json"; Path = (Join-Path $root "package-lock.json"); Required = $true },
        [pscustomobject]@{ Label = "python_typecheck"; Path = (Join-Path $root "python_typecheck"); Required = $true },
        [pscustomobject]@{ Label = "typescript/frontend.cjs"; Path = (Join-Path $root "typescript/frontend.cjs"); Required = $true },
        [pscustomobject]@{ Label = "node_modules/typescript"; Path = (Join-Path $root "node_modules/typescript"); Required = $true },
        [pscustomobject]@{ Label = "nagini_contracts"; Path = (Join-Path $naginiRoot "nagini_contracts"); Required = $true },
        [pscustomobject]@{ Label = "scripts/package-windows.ps1"; Path = (Join-Path $root "scripts/package-windows.ps1"); Required = $true },
        [pscustomobject]@{ Label = "scripts/package-input-snapshot.ps1"; Path = (Join-Path $root "scripts/package-input-snapshot.ps1"); Required = $true }
    )
}

function Get-MaledictusPackageInputSnapshot {
    param(
        [Parameter(Mandatory = $true)]
        [object[]]$Inputs
    )

    $entries = [System.Collections.Generic.List[object]]::new()
    foreach ($input in $Inputs) {
        $label = [string]$input.Label
        $path = [System.IO.Path]::GetFullPath([string]$input.Path)
        $required = [bool]$input.Required
        if ([string]::IsNullOrWhiteSpace($label)) {
            throw "package input labels must be nonempty"
        }
        if (-not (Test-Path -LiteralPath $path)) {
            if ($required) {
                throw "required package input does not exist: $label ($path)"
            }
            $entries.Add([pscustomobject]@{ LogicalPath = $label; Hash = "missing" })
            continue
        }
        if (Test-Path -LiteralPath $path -PathType Leaf) {
            $entries.Add([pscustomobject]@{
                LogicalPath = $label
                Hash = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant()
            })
            continue
        }
        if (-not (Test-Path -LiteralPath $path -PathType Container)) {
            throw "package input is neither a regular file nor a directory: $label ($path)"
        }
        $prefix = $path.TrimEnd("\", "/") + [System.IO.Path]::DirectorySeparatorChar
        Get-ChildItem -LiteralPath $path -File -Recurse -Force |
            Sort-Object FullName |
            ForEach-Object {
                $relative = $_.FullName.Substring($prefix.Length).Replace("\", "/")
                $entries.Add([pscustomobject]@{
                    LogicalPath = "$label/$relative"
                    Hash = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash.ToLowerInvariant()
                })
            }
    }

    $ordered = [System.Collections.Generic.SortedDictionary[string, string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($entry in $entries) {
        $logicalPath = [string]$entry.LogicalPath
        if ($ordered.ContainsKey($logicalPath)) {
            throw "duplicate package input path: $logicalPath"
        }
        $ordered.Add($logicalPath, [string]$entry.Hash)
    }
    $stream = [System.IO.MemoryStream]::new()
    try {
        foreach ($entry in $ordered.GetEnumerator()) {
            $logicalPath = [string]$entry.Key
            $pathBytes = [System.Text.Encoding]::UTF8.GetBytes($logicalPath)
            $hashBytes = [System.Text.Encoding]::ASCII.GetBytes([string]$entry.Value)
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
            return ([BitConverter]::ToString(
                $sha256.ComputeHash($stream.ToArray())
            )).Replace("-", "").ToLowerInvariant()
        } finally {
            $sha256.Dispose()
        }
    } finally {
        $stream.Dispose()
    }
}

function Assert-MaledictusPackageInputsUnchanged {
    param(
        [Parameter(Mandatory = $true)]
        [object[]]$Inputs,
        [Parameter(Mandatory = $true)]
        [string]$ExpectedSnapshot
    )

    $actualSnapshot = Get-MaledictusPackageInputSnapshot -Inputs $Inputs
    if ($actualSnapshot -cne $ExpectedSnapshot) {
        throw (
            "package-affecting inputs changed during the build: " +
            "expected snapshot $ExpectedSnapshot, observed $actualSnapshot; rerun from a stable source tree"
        )
    }
}
