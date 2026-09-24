param(
    [Parameter(Mandatory = $true)]
    [string]$TranslationPath,
    [Parameter(Mandatory = $true)]
    [string]$NormalizedProofPath,
    [Parameter(Mandatory = $true)]
    [string]$OutputPath
)

$ErrorActionPreference = "Stop"
$translation = Get-Content -LiteralPath $TranslationPath -Raw | ConvertFrom-Json
$proof = [IO.File]::ReadAllText((Resolve-Path -LiteralPath $NormalizedProofPath).Path)

$proof = $proof.Replace(
    "import VcTermSortProofs.TerminationMeasure",
    "import VcTermSortProofs.TerminationMeasure`nimport VcTermSortProofs.RawDecreaseProofs`nimport VcTermSort.Code.RawFuns"
)
$proof = $proof.Replace(
    "namespace VcTermSort.Proofs",
    "namespace VcTermSort.RawProofs`n`nopen VcTermSort.Proofs"
)
$proof = $proof.Replace(
    "end VcTermSort.Proofs",
    "end VcTermSort.RawProofs"
)

$localNames = @($translation.functions |
    Where-Object { $_.is_local -eq $true -and $_.is_opaque -eq $false } |
    ForEach-Object { [string]$_.lean_name } |
    Where-Object { $_.StartsWith("VcTermSort.") } |
    Sort-Object Length -Descending)

foreach ($name in $localNames) {
    $rawName = "VcTermSortRaw." + $name.Substring("VcTermSort.".Length)
    $proof = $proof.Replace($name, $rawName)
}

$proof = $proof.Replace(
    "run_loop_fuel_terminates_of_invariant",
    "raw_loop_terminates_of_invariant"
)

$loopStart = $proof.IndexOf("/-- A fuel-normalized extracted loop")
$loopEnd = $proof.IndexOf("theorem slice_iterator_next_some_member", $loopStart)
if ($loopStart -lt 0 -or $loopEnd -lt 0) {
    throw "Could not locate normalized loop-termination theorem."
}
$rawLoopTheorem = @'
/-- The exact raw Aeneas partial loop cannot diverge when its invariant makes
    each body call total, continuations preserve the invariant, and the source
    measure strictly decreases. -/
theorem raw_loop_terminates_of_invariant
    {State Output : Type}
    (body : State __ARROW__ Result (ControlFlow State Output))
    (invariant : State __ARROW__ Prop) (measure : State __ARROW__ Nat)
    (bodyTerminates : __FORALL__ state, invariant state __ARROW__ Terminates (body state))
    (preserves : __FORALL__ state next, invariant state __ARROW__
      body state = .ok (.cont next) __ARROW__ invariant next)
    (decreases : __FORALL__ state next,
      body state = .ok (.cont next) __ARROW__ measure next < measure state)
    (state : State) :
    invariant state __ARROW__ Terminates (loop body state) := by
  intro stateInvariant
  unfold loop
  have currentTerminates := bodyTerminates state stateInvariant
  cases observed : body state with
  | div => simp [Terminates, observed] at currentTerminates
  | fail error => simp [Terminates, observed]
  | ok flow =>
      cases flow with
      | done output => simp [Terminates, observed]
      | cont next =>
          simp [observed]
          apply raw_loop_terminates_of_invariant body invariant measure
            bodyTerminates preserves decreases next
          __BULLET__ exact preserves state next stateInvariant observed
termination_by measure state
decreasing_by exact decreases state next observed

'@
$rawLoopTheorem = $rawLoopTheorem.Replace("__ARROW__", [string][char]0x2192)
$rawLoopTheorem = $rawLoopTheorem.Replace("__FORALL__", [string][char]0x2200)
$rawLoopTheorem = $rawLoopTheorem.Replace("__BULLET__", [string][char]0x00B7)
$proof = $proof.Substring(0, $loopStart) + $rawLoopTheorem + $proof.Substring($loopEnd)
$proof = $proof.Replace("  $([char]0x00B7) simp [sliceIteratorRemaining]`r`n", "")
$proof = $proof.Replace("  $([char]0x00B7) simp [sliceIteratorRemaining]`n", "")

$accumulatorStart = $proof.IndexOf("theorem sort_bool_accumulator_loop_terminates")
$accumulatorEnd = $proof.IndexOf("theorem all_list_element_sorts_loop_terminates", $accumulatorStart)
if ($accumulatorStart -lt 0 -or $accumulatorEnd -lt 0) {
    throw "Could not locate the normalized sort-accumulator loop theorem."
}
$rawAccumulatorTheorem = @'
theorem sort_bool_accumulator_loop_terminates
    (predicate : VcTermSort.Sort __ARROW__ Result Bool)
    (body : core.slice.iter.Iter VcTermSort.Sort __ARROW__ Bool __ARROW__
      Result (ControlFlow (core.slice.iter.Iter VcTermSort.Sort __TIMES__ Bool) Bool))
    (iter : core.slice.iter.Iter VcTermSort.Sort) (result : Bool)
    (bodyTerminates : __FORALL__ state : core.slice.iter.Iter VcTermSort.Sort __TIMES__ Bool,
      (__FORALL__ child, child __MEMBER__ state.1.slice.val __ARROW__ Terminates (predicate child)) __ARROW__
      Terminates (body state.1 state.2))
    (bodyPreserves : __FORALL__ state next :
      core.slice.iter.Iter VcTermSort.Sort __TIMES__ Bool,
      body state.1 state.2 = .ok (.cont next) __ARROW__
      next.1.slice = state.1.slice)
    (bodyDecreases : __FORALL__ state next :
      core.slice.iter.Iter VcTermSort.Sort __TIMES__ Bool,
      body state.1 state.2 = .ok (.cont next) __ARROW__
      sliceIteratorRemaining next.1 < sliceIteratorRemaining state.1)
    (childrenTerminate : __FORALL__ child, child __MEMBER__ iter.slice.val __ARROW__
      Terminates (predicate child)) :
    Terminates (loop (fun state => body state.1 state.2) (iter, result)) := by
  apply raw_loop_terminates_of_invariant
    (fun state : core.slice.iter.Iter VcTermSort.Sort __TIMES__ Bool =>
      body state.1 state.2)
    (fun state => __FORALL__ child, child __MEMBER__ state.1.slice.val __ARROW__
      Terminates (predicate child))
    (fun state => sliceIteratorRemaining state.1)
  __BULLET__ intro state invariant
    exact bodyTerminates state invariant
  __BULLET__ intro state next invariant continued child member
    apply invariant child
    have slicesEqual := bodyPreserves state next continued
    simpa [slicesEqual] using member
  __BULLET__ intro state next continued
    exact bodyDecreases state next continued
  __BULLET__ exact childrenTerminate

'@
$rawAccumulatorTheorem = $rawAccumulatorTheorem.Replace("__ARROW__", [string][char]0x2192)
$rawAccumulatorTheorem = $rawAccumulatorTheorem.Replace("__FORALL__", [string][char]0x2200)
$rawAccumulatorTheorem = $rawAccumulatorTheorem.Replace("__TIMES__", [string][char]0x00D7)
$rawAccumulatorTheorem = $rawAccumulatorTheorem.Replace("__MEMBER__", [string][char]0x2208)
$rawAccumulatorTheorem = $rawAccumulatorTheorem.Replace("__BULLET__", [string][char]0x00B7)
$proof = $proof.Substring(0, $accumulatorStart) +
    $rawAccumulatorTheorem +
    $proof.Substring($accumulatorEnd)

$proof = $proof.Replace(
    "  rw [entrypoint_is_term_sort]`r`n  exact term_sort_terminates term",
    "  unfold VcTermSortRaw.term_sort_extraction_entrypoint`r`n  exact term_sort_terminates term"
)
$proof = $proof.Replace(
    "  rw [entrypoint_is_term_sort]`n  exact term_sort_terminates term",
    "  unfold VcTermSortRaw.term_sort_extraction_entrypoint`n  exact term_sort_terminates term"
)

$output = [IO.Path]::GetFullPath($OutputPath)
[IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($output)) | Out-Null
[IO.File]::WriteAllText($output, $proof, [Text.UTF8Encoding]::new($false))
