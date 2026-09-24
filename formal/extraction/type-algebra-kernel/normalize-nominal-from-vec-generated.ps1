param(
    [Parameter(Mandatory = $true)]
    [string] $RawDirectory,

    [Parameter(Mandatory = $true)]
    [string] $OutputDirectory
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$rawRoot = (Resolve-Path -LiteralPath $RawDirectory).Path
$rawCode = Join-Path $rawRoot "TypeAlgebraNominal/Code"
$rawTypes = Join-Path $rawCode "Types.lean"
$rawFuns = Join-Path $rawCode "Funs.lean"
$rawTranslation = Join-Path $rawRoot "translation.json"
foreach ($path in @($rawTypes, $rawFuns, $rawTranslation)) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
        throw "Missing focused generated artifact: $path"
    }
}

$types = [IO.File]::ReadAllText($rawTypes, [Text.Encoding]::UTF8)
$discriminant = "@[discriminant isize]`ninductive python_type_algebra_kernel.NominalClassList"
$firstDiscriminant = $types.IndexOf($discriminant, [StringComparison]::Ordinal)
$lastDiscriminant = $types.LastIndexOf($discriminant, [StringComparison]::Ordinal)
if ($firstDiscriminant -lt 0 -or $firstDiscriminant -ne $lastDiscriminant) {
    throw "Expected exactly one focused NominalClassList discriminant attribute."
}
$normalizedTypes = $types.Replace(
    $discriminant,
    "inductive python_type_algebra_kernel.NominalClassList"
)

$funs = [IO.File]::ReadAllText($rawFuns, [Text.Encoding]::UTF8)
$rawImport = "import TypeAlgebraNominal.Code.FunsExternal"
$normalizedImport = "import TypeAlgebraKernel.Code.FunsExternal"
$firstImport = $funs.IndexOf($rawImport, [StringComparison]::Ordinal)
$lastImport = $funs.LastIndexOf($rawImport, [StringComparison]::Ordinal)
if ($firstImport -lt 0 -or $firstImport -ne $lastImport) {
    throw "Expected exactly one generated focused external-model import."
}
$normalizedFuns = $funs.Replace($rawImport, $normalizedImport)

$outputRoot = [IO.Path]::GetFullPath($OutputDirectory)
$outputCode = Join-Path $outputRoot "TypeAlgebraNominal/Code"
[IO.Directory]::CreateDirectory($outputCode) | Out-Null
$utf8 = [Text.UTF8Encoding]::new($false)
[IO.File]::WriteAllText((Join-Path $outputCode "Types.lean"), $normalizedTypes, $utf8)
[IO.File]::WriteAllText((Join-Path $outputCode "Funs.lean"), $normalizedFuns, $utf8)
[IO.File]::WriteAllBytes(
    (Join-Path $outputRoot "nominal-from-vec-translation.json"),
    [IO.File]::ReadAllBytes($rawTranslation)
)

Write-Output "Normalized the focused generated namespace without changing function bodies."
