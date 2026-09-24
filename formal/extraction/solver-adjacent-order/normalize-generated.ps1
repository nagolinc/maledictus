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

function Replace-ExactlyOnce([string] $Text, [string] $Needle, [string] $Replacement) {
    if ((Get-OccurrenceCount $Text $Needle) -ne 1) {
        throw "Expected exactly one generated anchor: $Needle"
    }
    return $Text.Replace($Needle, $Replacement)
}

$rawRoot = (Resolve-Path -LiteralPath $RawDirectory).Path
$rawCode = Join-Path $rawRoot "SolverAdjacentOrder/Code"
$rawTypes = Join-Path $rawCode "Types.lean"
$rawFuns = Join-Path $rawCode "Funs.lean"
$rawTranslation = Join-Path $rawRoot "translation.json"
foreach ($path in @($rawTypes, $rawFuns, $rawTranslation)) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
        throw "Missing generated solver adjacent-order artifact: $path"
    }
}

$types = [IO.File]::ReadAllText($rawTypes, [Text.Encoding]::UTF8).Replace("`r`n", "`n")
if ((Get-OccurrenceCount $types "alloc.vec.Vec") -ne 16) {
    throw "Expected exactly sixteen generated Vec type occurrences."
}
$types = $types.Replace("alloc.vec.Vec", "_root_.List")
$types = Replace-ExactlyOnce $types `
    "Std.I64)`n`n/-- [maledictus::vc::Sort]" `
    "Std.I64)`nderiving BEq`n`n/-- [maledictus::vc::Sort]"
$types = Replace-ExactlyOnce $types `
    "`n`nmutual`n" `
    "`nderiving BEq`n`nmutual`n"
$types = Replace-ExactlyOnce $types `
    "end`n`ndef vc.PermissionTransferAmount.receiver" `
    "end`n`nderiving instance BEq for vc.PermissionTransferAmount, vc.Term`n`ndef vc.PermissionTransferAmount.receiver"

$funs = [IO.File]::ReadAllText($rawFuns, [Text.Encoding]::UTF8).Replace("`r`n", "`n")
if ((Get-OccurrenceCount $funs "alloc.vec.Vec") -ne 3) {
    throw "Expected exactly three generated Vec operation occurrences."
}
$funs = $funs.Replace("alloc.vec.Vec", "SolverAdjacentOrder.ModelVec")
$rawLoop = "  loop`n"
if ((Get-OccurrenceCount $funs $rawLoop) -ne 1) {
    throw "Expected exactly one generated unwrap loop invocation."
}
$funs = $funs.Replace($rawLoop, "  runLoopFuel (sizeOf term + 1)`n")

$outputRoot = [IO.Path]::GetFullPath($OutputDirectory)
$outputCode = Join-Path $outputRoot "SolverAdjacentOrder/Code"
[IO.Directory]::CreateDirectory($outputCode) | Out-Null
$utf8 = [Text.UTF8Encoding]::new($false)
[IO.File]::WriteAllText((Join-Path $outputCode "Types.lean"), $types, $utf8)
[IO.File]::WriteAllText((Join-Path $outputCode "Funs.lean"), $funs, $utf8)
[IO.File]::WriteAllBytes(
    (Join-Path $outputRoot "translation.json"),
    [IO.File]::ReadAllBytes($rawTranslation)
)

Write-Output "Normalized sixteen recursive Vec types, three Vec operations, and one finite source loop."
