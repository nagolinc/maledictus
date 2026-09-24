param(
    [Parameter(Mandatory = $true)]
    [string]$TranslationPath,
    [Parameter(Mandatory = $true)]
    [string]$ConcreteProofPath,
    [Parameter(Mandatory = $true)]
    [string]$OutputPath
)

$ErrorActionPreference = "Stop"
$translation = Get-Content -LiteralPath $TranslationPath -Raw | ConvertFrom-Json
$source = [IO.File]::ReadAllText((Resolve-Path -LiteralPath $ConcreteProofPath).Path)
$names = @(
    "all_list_element_sorts_body_decreases",
    "all_finite_dict_key_sorts_body_decreases",
    "all_finite_dict_value_sorts_body_decreases",
    "require_variadic_tuple_element_sorts_body_decreases",
    "all_nominal_references_body_decreases",
    "all_nominal_reference_keys_body_decreases",
    "validate_int_enum_descriptor_body_decreases",
    "require_predicate_argument_sorts_body_decreases",
    "require_permission_transfer_amounts_body_decreases",
    "require_all_sorts_body_decreases",
    "collect_sorts_body_decreases",
    "require_finite_dict_entry_sorts_body_decreases",
    "validate_bound_occurrences_all_body_decreases",
    "validate_bound_occurrences_all_transfers_body_decreases",
    "validate_bound_occurrences_all_entries_body_decreases"
)

$pieces = [Collections.Generic.List[string]]::new()
$continuationStart = $source.IndexOf("def continuationIterator")
$continuationEnd = $source.IndexOf("`ntheorem ", $continuationStart)
if ($continuationStart -lt 0 -or $continuationEnd -lt 0) {
    throw "Missing continuation iterator projection helper."
}
$pieces.Add($source.Substring(
    $continuationStart,
    $continuationEnd - $continuationStart
).TrimEnd())
$helperStart = $source.IndexOf("theorem two_bind_cont_iterator_first")
$helperEnd = $source.IndexOf("theorem require_all_sorts_body_decreases", $helperStart)
if ($helperStart -lt 0 -or $helperEnd -lt 0) {
    throw "Missing shared continuation-decomposition helpers."
}
$pieces.Add($source.Substring($helperStart, $helperEnd - $helperStart).TrimEnd())
foreach ($name in $names) {
    $start = $source.IndexOf("theorem $name")
    if ($start -lt 0) {
        throw "Missing decrease theorem: $name"
    }
    $next = $source.IndexOf("`ntheorem ", $start + 1)
    if ($next -lt 0) {
        throw "Missing theorem boundary after: $name"
    }
    $pieces.Add($source.Substring($start, $next - $start).TrimEnd())
}

$proof = "import VcTermSortProofs.Foundation`nimport VcTermSort.Code.RawFuns`n`n" +
    "open Aeneas Aeneas.Std Result ControlFlow Error`n" +
    "set_option maxHeartbeats 2000000`n`n" +
    "namespace VcTermSort.RawProofs`n`nopen VcTermSort.Proofs`n`n" +
    ($pieces -join "`n`n") + "`n`nend VcTermSort.RawProofs`n"

$localNames = @($translation.functions |
    Where-Object { $_.is_local -eq $true -and $_.is_opaque -eq $false } |
    ForEach-Object { [string]$_.lean_name } |
    Where-Object { $_.StartsWith("VcTermSort.") } |
    Sort-Object Length -Descending)
foreach ($name in $localNames) {
    $rawName = "VcTermSortRaw." + $name.Substring("VcTermSort.".Length)
    $proof = $proof.Replace($name, $rawName)
}

$output = [IO.Path]::GetFullPath($OutputPath)
[IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($output)) | Out-Null
[IO.File]::WriteAllText($output, $proof, [Text.UTF8Encoding]::new($false))
