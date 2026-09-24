param(
    [Parameter(Mandatory = $true)]
    [string]$RawCodeRoot,
    [Parameter(Mandatory = $true)]
    [string]$OutputCodeRoot
)

$ErrorActionPreference = "Stop"

function Replace-ExactCount {
    param(
        [string]$Text,
        [string]$Old,
        [string]$New,
        [int]$Expected,
        [string]$Label
    )

    $actual = ([regex]::Matches($Text, [regex]::Escape($Old))).Count
    if ($actual -ne $Expected) {
        throw "Normalization input drift for ${Label}: expected ${Expected}, found ${actual}."
    }
    return $Text.Replace($Old, $New)
}

$rawRoot = (Resolve-Path -LiteralPath $RawCodeRoot).Path
$typesPath = Join-Path $rawRoot "Types.lean"
$funsPath = Join-Path $rawRoot "Funs.lean"
if (-not (Test-Path -LiteralPath $typesPath -PathType Leaf)) {
    throw "Missing raw Aeneas Types.lean: $typesPath"
}
if (-not (Test-Path -LiteralPath $funsPath -PathType Leaf)) {
    throw "Missing raw Aeneas Funs.lean: $funsPath"
}

$outputRoot = [IO.Path]::GetFullPath($OutputCodeRoot)
[IO.Directory]::CreateDirectory($outputRoot) | Out-Null
$utf8 = [Text.UTF8Encoding]::new($false)

$types = [IO.File]::ReadAllText($typesPath)
$types = Replace-ExactCount $types "alloc.vec.Vec" "_root_.List" 16 "recursive Vec types"
$arrow = [char]0x2192
$types = Replace-ExactCount $types "| Bool : Bool $arrow Term" "| Bool : _root_.Bool $arrow Term" 1 "Bool constructor payload"

$funs = [IO.File]::ReadAllText($funsPath)
$funs = Replace-ExactCount $funs "alloc.vec.Vec" "VcTermSort.ModelVec" 42 "Vec operations"
$funs = Replace-ExactCount $funs "core.cmp.PartialOrd.gt.default`n    alloc.string.String.Insts.CoreCmpPartialOrdString" "core.cmp.PartialOrd.gt.default`n    alloc.string.String.Insts.CoreCmpPartialOrdString.partial_cmp" 1 "Aeneas String PartialOrd emitter"
$funs = Replace-ExactCount $funs "Result Bool" "Result _root_.Bool" 17 "Bool result types"
$funs = Replace-ExactCount $funs "(result : Bool)" "(result : _root_.Bool)" 10 "Bool accumulator parameters"
$funs = Replace-ExactCount $funs "(valid : Bool)" "(valid : _root_.Bool)" 2 "Bool validity parameters"
$funs = Replace-ExactCount $funs "core.result.Result Unit" "core.result.Result _root_.Unit" 55 "unit result payloads"

# Preserve the exact Aeneas partial-fixpoint program in a separate namespace
# before replacing its eleven finite slice-loop calls.  The proof project
# imports this mechanically derived twin and proves each changed wrapper equal
# to the normalized one, so the normalization is not a trusted text rewrite.
$rawFuns = Replace-ExactCount $funs "namespace VcTermSort" "namespace VcTermSortRaw`n`nopen VcTermSort" 1 "raw namespace"
$rawFuns = Replace-ExactCount $rawFuns "end VcTermSort" "end VcTermSortRaw" 1 "raw namespace end"
$funs = Replace-ExactCount $funs "  loop`n" "  VcTermSort.runLoopFuel (iter.slice.val.length - iter.i + 1)`n" 15 "finite slice loops"

[IO.File]::WriteAllText((Join-Path $outputRoot "Types.lean"), $types, $utf8)
[IO.File]::WriteAllText((Join-Path $outputRoot "Funs.lean"), $funs, $utf8)
[IO.File]::WriteAllText((Join-Path $outputRoot "RawFuns.lean"), $rawFuns, $utf8)
