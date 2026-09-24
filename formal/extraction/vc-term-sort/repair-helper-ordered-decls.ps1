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
    $translated.options.start_from[0] -ne "crate::ObligationResult::satisfied") {
    throw "Expected the focused ObligationResult::satisfied extraction root."
}
if ($translated.type_decls.Count -ne 5 -or $translated.fun_decls.Count -ne 1 -or
    $translated.trait_decls.Count -ne 0 -or $translated.trait_impls.Count -ne 0 -or
    $translated.ordered_decls.Count -ne 0) {
    throw "Focused helper declaration inventory changed; refusing to repair ordering."
}

$function = $translated.fun_decls[0]
if ($function.item_meta.source_text -notmatch "pub fn satisfied") {
    throw "The sole extracted function is not ObligationResult::satisfied."
}
if ($function.item_meta.opacity -ne "Transparent" -or $null -eq $function.body) {
    throw "ObligationResult::satisfied is not a transparent extracted body."
}

$raw = Get-Content -LiteralPath $inputFile -Raw
$marker = '"ordered_decls":[]'
$replacement = '"ordered_decls":[' +
    '{"Type":{"NonRec":1}},' +
    '{"Type":{"NonRec":2}},' +
    '{"Type":{"NonRec":3}},' +
    '{"Type":{"NonRec":4}},' +
    '{"Type":{"NonRec":0}},' +
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
if ($repaired.translated.ordered_decls.Count -ne 6) {
    throw "Repaired helper extraction does not contain the expected declaration ordering."
}

Write-Output "Repaired the focused helper declaration order without changing extracted declarations."
