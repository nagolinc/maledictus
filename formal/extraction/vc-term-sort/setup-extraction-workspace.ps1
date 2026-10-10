param(
    [string]$RepositoryRoot,
    [string]$WorkspacePath,
    [switch]$ValidateOnly
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

function Get-NormalizedPath {
    param([Parameter(Mandatory = $true)][string]$Path)

    return [IO.Path]::GetFullPath($Path).TrimEnd(
        [IO.Path]::DirectorySeparatorChar,
        [IO.Path]::AltDirectorySeparatorChar
    )
}

function Test-IsDirectChild {
    param(
        [Parameter(Mandatory = $true)][string]$Candidate,
        [Parameter(Mandatory = $true)][string]$Parent
    )

    $normalizedCandidate = Get-NormalizedPath $Candidate
    $normalizedParent = Get-NormalizedPath $Parent
    $candidateParent = Get-NormalizedPath ([IO.Path]::GetDirectoryName($normalizedCandidate))
    return $candidateParent.Equals(
        $normalizedParent,
        [StringComparison]::OrdinalIgnoreCase
    )
}

function Assert-PhysicalDirectory {
    param(
        [Parameter(Mandatory = $true)][string]$Path,
        [Parameter(Mandatory = $true)][string]$Description
    )

    if (-not (Test-Path -LiteralPath $Path)) {
        return
    }
    if (-not (Test-Path -LiteralPath $Path -PathType Container)) {
        throw "$Description is not a directory: $Path"
    }
    $directory = Get-Item -LiteralPath $Path -Force
    if (-not [string]::IsNullOrEmpty([string]$directory.LinkType)) {
        throw "$Description must be a physical directory, not $($directory.LinkType): $Path"
    }
}

function Assert-ExactFile {
    param(
        [Parameter(Mandatory = $true)][string]$Actual,
        [Parameter(Mandatory = $true)][string]$Expected,
        [Parameter(Mandatory = $true)][string]$Description
    )

    if (-not (Test-Path -LiteralPath $Actual -PathType Leaf)) {
        throw "Missing $Description at $Actual."
    }
    $actualHash = (Get-FileHash -LiteralPath $Actual -Algorithm SHA256).Hash
    $expectedHash = (Get-FileHash -LiteralPath $Expected -Algorithm SHA256).Hash
    if ($actualHash -ne $expectedHash) {
        throw "$Description at $Actual does not match $Expected. Refusing to overwrite it."
    }
}

function Test-SameWindowsFile {
    param(
        [Parameter(Mandatory = $true)][string]$First,
        [Parameter(Mandatory = $true)][string]$Second
    )

    # PowerShell 7 does not populate FileInfo.Target for hard links. Compare
    # the open files' volume and file identifiers instead of path display
    # metadata or content hashes, which cannot distinguish an identical copy.
    if ($null -eq ("Maledictus.Extraction.WindowsFileIdentity" -as [type])) {
        Add-Type -TypeDefinition @'
using System;
using System.ComponentModel;
using System.IO;
using System.Runtime.InteropServices;
using Microsoft.Win32.SafeHandles;

namespace Maledictus.Extraction
{
    public static class WindowsFileIdentity
    {
        [StructLayout(LayoutKind.Sequential)]
        private struct FileInformation
        {
            public uint FileAttributes;
            public System.Runtime.InteropServices.ComTypes.FILETIME CreationTime;
            public System.Runtime.InteropServices.ComTypes.FILETIME LastAccessTime;
            public System.Runtime.InteropServices.ComTypes.FILETIME LastWriteTime;
            public uint VolumeSerialNumber;
            public uint FileSizeHigh;
            public uint FileSizeLow;
            public uint NumberOfLinks;
            public uint FileIndexHigh;
            public uint FileIndexLow;
        }

        [DllImport("kernel32.dll", SetLastError = true)]
        [return: MarshalAs(UnmanagedType.Bool)]
        private static extern bool GetFileInformationByHandle(
            SafeFileHandle handle, out FileInformation information);

        private static FileInformation ReadInformation(FileStream stream)
        {
            FileInformation information;
            if (!GetFileInformationByHandle(stream.SafeFileHandle, out information))
            {
                throw new Win32Exception(Marshal.GetLastWin32Error());
            }
            return information;
        }

        public static bool SameFile(string first, string second)
        {
            // Keep both handles open so neither identity can be reused while
            // comparing them. These checks never modify either file.
            using (var firstStream = File.Open(first, FileMode.Open, FileAccess.Read,
                FileShare.ReadWrite | FileShare.Delete))
            using (var secondStream = File.Open(second, FileMode.Open, FileAccess.Read,
                FileShare.ReadWrite | FileShare.Delete))
            {
                var firstInfo = ReadInformation(firstStream);
                var secondInfo = ReadInformation(secondStream);
                return firstInfo.VolumeSerialNumber == secondInfo.VolumeSerialNumber
                    && firstInfo.FileIndexHigh == secondInfo.FileIndexHigh
                    && firstInfo.FileIndexLow == secondInfo.FileIndexLow;
            }
        }
    }
}
'@
    }
    return [Maledictus.Extraction.WindowsFileIdentity]::SameFile($First, $Second)
}

$scriptRoot = Get-NormalizedPath $PSScriptRoot
if ([string]::IsNullOrWhiteSpace($RepositoryRoot)) {
    $RepositoryRoot = Join-Path $scriptRoot "..\..\.."
}
$repository = Get-NormalizedPath $RepositoryRoot
if (-not (Test-Path -LiteralPath $repository -PathType Container)) {
    throw "Repository root does not exist: $repository"
}
Assert-PhysicalDirectory -Path $repository -Description "repository root"

$cacheRoot = Get-NormalizedPath (Join-Path $repository ".cache")
if ([string]::IsNullOrWhiteSpace($WorkspacePath)) {
    $WorkspacePath = Join-Path $cacheRoot "vc-term-sort-extraction"
}
$workspace = Get-NormalizedPath $WorkspacePath
if (-not (Test-IsDirectChild -Candidate $workspace -Parent $cacheRoot)) {
    throw "Extraction workspace must be a direct child of the repository cache directory: $cacheRoot"
}
Assert-PhysicalDirectory -Path $cacheRoot -Description "repository cache"
Assert-PhysicalDirectory -Path $workspace -Description "extraction workspace"

$source = Get-NormalizedPath (Join-Path $repository "src\vc.rs")
$templateManifest = Get-NormalizedPath (Join-Path $scriptRoot "Cargo.toml")
if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
    throw "Production Term::sort source does not exist: $source"
}
if (-not (Test-Path -LiteralPath $templateManifest -PathType Leaf)) {
    throw "Extraction Cargo template does not exist: $templateManifest"
}

$workspaceManifest = Join-Path $workspace "Cargo.toml"
$workspaceSourceDirectory = Join-Path $workspace "src"
$workspaceSource = Join-Path $workspaceSourceDirectory "lib.rs"
Assert-PhysicalDirectory -Path $workspaceSourceDirectory `
    -Description "extraction source directory"

if ($ValidateOnly) {
    if (-not (Test-Path -LiteralPath $workspace -PathType Container)) {
        throw "Extraction workspace does not exist: $workspace"
    }
} else {
    [IO.Directory]::CreateDirectory($workspace) | Out-Null
    [IO.Directory]::CreateDirectory($workspaceSourceDirectory) | Out-Null
    Assert-PhysicalDirectory -Path $workspace -Description "extraction workspace"
    Assert-PhysicalDirectory -Path $workspaceSourceDirectory `
        -Description "extraction source directory"
    if (-not (Test-Path -LiteralPath $workspaceManifest)) {
        [IO.File]::Copy($templateManifest, $workspaceManifest, $false)
    }
}

Assert-ExactFile -Actual $workspaceManifest -Expected $templateManifest `
    -Description "extraction Cargo manifest"

if (-not (Test-Path -LiteralPath $workspaceSource)) {
    if ($ValidateOnly) {
        throw "Extraction source hard link does not exist: $workspaceSource"
    }
    [IO.Directory]::CreateDirectory($workspaceSourceDirectory) | Out-Null
    New-Item -ItemType HardLink -Path $workspaceSource -Target $source | Out-Null
}

if (-not (Test-Path -LiteralPath $workspaceSource -PathType Leaf)) {
    throw "Extraction source path is not a file: $workspaceSource"
}
$link = Get-Item -LiteralPath $workspaceSource -Force
if ($link.LinkType -ne "HardLink") {
    throw "Extraction source must be a hard link, not a copied or symbolic file: $workspaceSource"
}

if (-not (Test-SameWindowsFile -First $workspaceSource -Second $source)) {
    throw "Extraction source hard link is not production source $source`: $workspaceSource"
}

Assert-ExactFile -Actual $workspaceSource -Expected $source `
    -Description "extraction source hard link"

Write-Output "vc-term-sort extraction workspace valid"
Write-Output "workspace: $workspace"
Write-Output "source hard link: $workspaceSource -> $source"
