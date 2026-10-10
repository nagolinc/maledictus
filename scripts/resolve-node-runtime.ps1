function Resolve-MaledictusNodeRuntime {
    if (-not [string]::IsNullOrWhiteSpace($env:MALEDICTUS_NODE)) {
        $runtimePath = (Resolve-Path -LiteralPath $env:MALEDICTUS_NODE -ErrorAction Stop).Path
    } else {
        # PowerShell returns every matching application when several Node
        # installations are on PATH. Select the executable command resolution
        # will actually use, not an array coerced into one invalid command name.
        $runtimePath = (Get-Command node -CommandType Application -ErrorAction Stop |
            Select-Object -First 1).Source
    }
    if (-not (Test-Path -LiteralPath $runtimePath -PathType Leaf)) {
        throw "packaged TypeScript verification selected a missing Node executable"
    }
    return $runtimePath
}
