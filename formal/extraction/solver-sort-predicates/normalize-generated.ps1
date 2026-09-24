param(
    [Parameter(Mandatory = $true)]
    [string] $RawDirectory,

    [Parameter(Mandatory = $true)]
    [string] $OutputDirectory
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

function Get-OccurrenceCount([string] $Text, [string] $Needle) {
    $count = 0
    $offset = 0
    while (($found = $Text.IndexOf($Needle, $offset, [StringComparison]::Ordinal)) -ge 0) {
        $count += 1
        $offset = $found + $Needle.Length
    }
    return $count
}

$rawRoot = (Resolve-Path -LiteralPath $RawDirectory).Path
$rawCode = Join-Path $rawRoot "SolverSortPredicates/Code"
$rawTypes = Join-Path $rawCode "Types.lean"
$rawFuns = Join-Path $rawCode "Funs.lean"
$rawTranslation = Join-Path $rawRoot "translation.json"
foreach ($path in @($rawTypes, $rawFuns, $rawTranslation)) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
        throw "Missing generated solver-sort artifact: $path"
    }
}

$types = [IO.File]::ReadAllText($rawTypes, [Text.Encoding]::UTF8).Replace("`r`n", "`n")
$rawTuple = "Tuple : alloc.vec.Vec vc.Sort"
if ((Get-OccurrenceCount $types $rawTuple) -ne 1) {
    throw "Expected exactly one recursive vc.Sort tuple vector in generated Types.lean."
}
$normalizedTypes = $types.Replace($rawTuple, "Tuple : _root_.List vc.Sort")

$funs = [IO.File]::ReadAllText($rawFuns, [Text.Encoding]::UTF8).Replace("`r`n", "`n")
$rawLoop = "  loop`n"
if ((Get-OccurrenceCount $funs $rawLoop) -ne 3) {
    throw "Expected exactly three generated solver-sort loop invocations."
}
$normalizedFuns = $funs.Replace(
    $rawLoop,
    "  runLoopFuel (iter.slice.val.length - iter.i + 1)`n"
)

$outputRoot = [IO.Path]::GetFullPath($OutputDirectory)
$outputCode = Join-Path $outputRoot "SolverSortPredicates/Code"
[IO.Directory]::CreateDirectory($outputCode) | Out-Null
$utf8 = [Text.UTF8Encoding]::new($false)
[IO.File]::WriteAllText((Join-Path $outputCode "Types.lean"), $normalizedTypes, $utf8)
[IO.File]::WriteAllText((Join-Path $outputCode "Funs.lean"), $normalizedFuns, $utf8)
[IO.File]::WriteAllBytes(
    (Join-Path $outputRoot "translation.json"),
    [IO.File]::ReadAllBytes($rawTranslation)
)

Write-Output "Normalized one recursive Vec representation and exactly three finite source loops."
