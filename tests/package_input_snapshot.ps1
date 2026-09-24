$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

. (Join-Path $PSScriptRoot "../scripts/package-input-snapshot.ps1")

$temporaryRoot = Join-Path (
    [System.IO.Path]::GetTempPath()
) ("maledictus-package-snapshot-test-" + [guid]::NewGuid().ToString("N"))
New-Item -ItemType Directory -Path $temporaryRoot -Force | Out-Null
try {
    $sourceRoot = Join-Path $temporaryRoot "src"
    New-Item -ItemType Directory -Path $sourceRoot -Force | Out-Null
    $sourceFile = Join-Path $sourceRoot "lib.rs"
    [System.IO.File]::WriteAllText($sourceFile, "pub fn value() -> i32 { 1 }`n")
    $inputs = @(
        [pscustomobject]@{ Label = "src"; Path = $sourceRoot; Required = $true },
        [pscustomobject]@{ Label = "optional"; Path = (Join-Path $temporaryRoot "optional"); Required = $false }
    )

    $initial = Get-MaledictusPackageInputSnapshot -Inputs $inputs
    Assert-MaledictusPackageInputsUnchanged -Inputs $inputs -ExpectedSnapshot $initial

    [System.IO.File]::WriteAllText($sourceFile, "pub fn value() -> i32 { 2 }`n")
    try {
        Assert-MaledictusPackageInputsUnchanged -Inputs $inputs -ExpectedSnapshot $initial
        throw "snapshot guard accepted a modified source input"
    } catch {
        if ($_.Exception.Message -notlike "package-affecting inputs changed during the build:*") {
            throw
        }
    }

    [System.IO.File]::WriteAllText(
        (Join-Path $temporaryRoot "optional"),
        "new optional build input`n"
    )
    $modified = Get-MaledictusPackageInputSnapshot -Inputs $inputs
    if ($modified -ceq $initial) {
        throw "snapshot guard ignored a newly created optional input"
    }
    Write-Output "package input snapshot guard detects modified and newly added inputs"
} finally {
    if (Test-Path -LiteralPath $temporaryRoot) {
        Remove-Item -LiteralPath $temporaryRoot -Recurse -Force
    }
}
