param(
    [Parameter(Mandatory = $true)]
    [string] $InputPath,

    [Parameter(Mandatory = $true)]
    [string] $OutputPath
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$inputFile = (Resolve-Path -LiteralPath $InputPath).Path
$document = Get-Content -LiteralPath $inputFile -Raw | ConvertFrom-Json
$translated = $document.translated

if ($translated.options.start_from.Count -ne 1 -or
    $translated.options.start_from[0] -ne
        "crate::python_type_algebra_kernel::NominalClassList::from_vec") {
    throw "Expected the focused NominalClassList::from_vec extraction root."
}
if ($translated.type_decls.Count -ne 6 -or $translated.fun_decls.Count -ne 9 -or
    $translated.trait_decls.Count -ne 1 -or $translated.trait_impls.Count -ne 6 -or
    $translated.ordered_decls.Count -ne 0) {
    throw "Focused NominalClassList::from_vec declaration inventory changed."
}

$function = $translated.fun_decls[0]
if (-not $function.item_meta.source_text.Contains("fn from_vec(mut classes")) {
    throw "The sole focused function is not NominalClassList::from_vec."
}
if ($function.item_meta.opacity -ne "Transparent" -or $null -eq $function.body) {
    throw "NominalClassList::from_vec is not a transparent extracted body."
}
if (-not $translated.type_decls[0].item_meta.source_text.Contains("enum NominalClassList") -or
    -not $translated.type_decls[1].item_meta.source_text.Contains("struct NominalClass")) {
    throw "Focused source-owned type declarations changed."
}

$raw = Get-Content -LiteralPath $inputFile -Raw
$marker = '"ordered_decls":[]'
$replacement = '"ordered_decls":[' +
    '{"Type":{"NonRec":4}},' +
    '{"TraitDecl":{"NonRec":0}},' +
    '{"Fun":{"NonRec":5}},' +
    '{"Type":{"NonRec":2}},' +
    '{"Fun":{"NonRec":7}},' +
    '{"Fun":{"NonRec":2}},' +
    '{"Type":{"NonRec":5}},' +
    '{"Fun":{"NonRec":8}},' +
    '{"Type":{"NonRec":3}},' +
    '{"Fun":{"NonRec":4}},' +
    '{"Fun":{"NonRec":1}},' +
    '{"Type":{"NonRec":1}},' +
    '{"Fun":{"NonRec":6}},' +
    '{"Type":{"Rec":[0]}},' +
    '{"Fun":{"NonRec":3}},' +
    '{"Fun":{"NonRec":0}}]'
$firstMarker = $raw.IndexOf($marker, [StringComparison]::Ordinal)
$lastMarker = $raw.LastIndexOf($marker, [StringComparison]::Ordinal)
if ($firstMarker -lt 0 -or $firstMarker -ne $lastMarker) {
    throw "Expected exactly one empty ordered_decls marker."
}

$outputFile = [IO.Path]::GetFullPath($OutputPath)
$outputDirectory = [IO.Path]::GetDirectoryName($outputFile)
[IO.Directory]::CreateDirectory($outputDirectory) | Out-Null
[IO.File]::WriteAllText(
    $outputFile,
    $raw.Replace($marker, $replacement),
    [Text.UTF8Encoding]::new($false)
)

$repaired = Get-Content -LiteralPath $outputFile -Raw | ConvertFrom-Json
if ($repaired.translated.ordered_decls.Count -ne 16) {
    throw "Repaired focused extraction does not contain the expected declaration ordering."
}

Write-Output "Repaired the focused declaration order without changing extracted declarations."
