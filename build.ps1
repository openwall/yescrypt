#requires -Version 5.1
<#
.COPYRIGHT
    Copyright 2013-2026 Alexander Peslyak
    Copyright 2026 CPUchain
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted.

    THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
    ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
    IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
    ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
    FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
    DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
    OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
    HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
    OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
    SUCH DAMAGE.

.SYNOPSIS
    Build yescrypt with the MSVC toolchain (port of the supplied GNU Makefile).

.DESCRIPTION
    Locates a Visual Studio / Build Tools installation with the C++ compiler
    using vswhere.exe, imports its x64 environment, and compiles the yescrypt
    "tests" and "phc-test" programs with cl.exe / link.exe.

    The Makefile's "initrom" and "userom" programs are intentionally NOT built:
    they rely on POSIX shared memory (sys/shm.h) and mmap, which have no MSVC
    equivalent.  "tests" and "phc-test" are what "make check" exercises.

    Targets (mirroring the Makefile):
        build.ps1                 # build tests.exe and phc-test.exe (optimized)
        build.ps1 -Target check   # build and run both, verify against known-good
        build.ps1 -Target ref     # build using the reference implementation
        build.ps1 -Target check-ref
        build.ps1 -Target clean   # remove build artifacts

.NOTES
    Requires Visual Studio 2026 (Community is fine) with the
    "Desktop development with C++" workload installed. See the README section
    "How to test yescrypt for proper operation." for details.
#>
[CmdletBinding()]
param(
    [ValidateSet('all', 'tests', 'phc-test', 'check', 'ref', 'check-ref', 'clean')]
    [string]$Target = 'all'
)

$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath $PSScriptRoot

# --- Toolchain detection via vswhere.exe ------------------------------------

function Find-VsWhere {
    $candidates = @(
        (Join-Path ${env:ProgramFiles(x86)} 'Microsoft Visual Studio\Installer\vswhere.exe'),
        (Join-Path $env:ProgramFiles 'Microsoft Visual Studio\Installer\vswhere.exe')
    )
    foreach ($c in $candidates) {
        if ($c -and (Test-Path -LiteralPath $c)) { return $c }
    }
    $cmd = Get-Command vswhere.exe -ErrorAction SilentlyContinue
    if ($cmd) { return $cmd.Source }
    throw "vswhere.exe not found. Install Visual Studio 2026 (it ships vswhere)."
}

function Get-VcVarsPath {
    $vswhere = Find-VsWhere
    # Require the x64/x86 C++ compiler toolset.
    $installPath = & $vswhere -latest -products * `
        -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 `
        -property installationPath
    if (-not $installPath) {
        throw "No Visual Studio installation with the C++ toolset was found. " +
              "Install the 'Desktop development with C++' workload."
    }
    $vcvars = Join-Path $installPath 'VC\Auxiliary\Build\vcvars64.bat'
    if (-not (Test-Path -LiteralPath $vcvars)) {
        throw "vcvars64.bat not found under '$installPath'."
    }
    return $vcvars
}

# Import the MSVC x64 environment (PATH, INCLUDE, LIB, ...) into this session.
function Import-VcEnvironment {
    $vcvars = Get-VcVarsPath
    Write-Host "Using MSVC environment: $vcvars"
    $marker = '___VCVARS_ENV___'
    # vcvars64.bat may emit benign stderr noise; don't let it abort the script.
    $lines = & cmd /c "`"$vcvars`" 2>nul && echo $marker && set"
    $seen = $false
    foreach ($line in $lines) {
        if (-not $seen) {
            if ($line.Trim() -eq $marker) { $seen = $true }
            continue
        }
        if ($line -match '^([^=]+)=(.*)$') {
            Set-Item -Path ("Env:" + $matches[1]) -Value $matches[2]
        }
    }
    if (-not $seen) { throw "Failed to import the MSVC environment." }
}

# --- Compiler / linker settings (port of Makefile CFLAGS) -------------------

# /O2            -> -O2
# /D__SSE2__     -> enable the SSE2 intrinsic code path (MSVC x64 supports
#                   <emmintrin.h>; this path is free of GCC inline asm).
# /DSKIP_MEMZERO -> matches the Makefile's -DSKIP_MEMZERO.
# OpenMP is intentionally not enabled: it is only used by userom, which is not
# built here.
$CFLAGS = @('/nologo', '/O2', '/MT', '/D__SSE2__', '/DSKIP_MEMZERO', '/wd4146', '/wd4244')

$OBJS_COMMON = @('yescrypt-common.obj', 'sha256.obj', 'insecure_memzero.obj')
$OBJS_CORE_OPT = 'yescrypt-opt.obj'
$OBJS_CORE_REF = 'yescrypt-ref.obj'

function Invoke-Tool {
    param([string]$Exe, [string[]]$Arguments)
    Write-Host ">> $Exe $($Arguments -join ' ')"
    # Send tool output to the host so it doesn't pollute function return values.
    & $Exe @Arguments | Out-Host
    if ($LASTEXITCODE -ne 0) {
        throw "$Exe failed with exit code $LASTEXITCODE"
    }
}

function Compile-One {
    param([string]$Source, [string]$Obj, [string[]]$ExtraFlags = @())
    if (-not $Obj) {
        $Obj = [System.IO.Path]::GetFileNameWithoutExtension($Source) + '.obj'
    }
    Invoke-Tool 'cl' (@('/c') + $CFLAGS + $ExtraFlags + @("/Fo$Obj", $Source))
    return $Obj
}

function Link-Exe {
    param([string]$Out, [string[]]$Objs)
    Invoke-Tool 'link' (@('/nologo', "/OUT:$Out") + $Objs)
}

# Compile the core + common objects shared by every program.
function Build-Common {
    param([string]$Core = $OBJS_CORE_OPT)
    $coreSrc = if ($Core -eq $OBJS_CORE_REF) { 'yescrypt-ref.c' } else { 'yescrypt-opt.c' }
    Compile-One $coreSrc $Core | Out-Null
    Compile-One 'yescrypt-common.c' 'yescrypt-common.obj' | Out-Null
    Compile-One 'sha256.c' 'sha256.obj' | Out-Null
    Compile-One 'insecure_memzero.c' 'insecure_memzero.obj' | Out-Null
}

function Build-Tests {
    param([string]$Core = $OBJS_CORE_OPT)
    Build-Common -Core $Core
    Compile-One 'tests.c' 'tests.obj' | Out-Null
    Link-Exe 'tests.exe' (@($Core) + $OBJS_COMMON + @('tests.obj'))
    Write-Host "Built tests.exe"
}

function Build-PhcTest {
    param([string]$Core = $OBJS_CORE_OPT)
    Build-Common -Core $Core
    # phc-test is phc.c compiled with -DTEST (Makefile: phc-test.o).
    Compile-One 'phc.c' 'phc-test.obj' @('/DTEST') | Out-Null
    Link-Exe 'phc-test.exe' (@($Core) + $OBJS_COMMON + @('phc-test.obj'))
    Write-Host "Built phc-test.exe"
}

# Read a file as text with CRLF normalized to LF (MSVC's text-mode output uses
# CRLF; the known-good files use LF).
function Get-NormalizedText {
    param([string]$Path)
    return (Get-Content -Raw -LiteralPath $Path) -replace "`r`n", "`n"
}

function Invoke-Check {
    param([string]$Core = $OBJS_CORE_OPT)
    Build-Tests -Core $Core
    Build-PhcTest -Core $Core

    Write-Host 'Running main tests'
    & .\tests.exe | Out-File -Encoding ascii -FilePath 'TESTS-OUT'
    if ($LASTEXITCODE -ne 0) { throw "tests.exe failed with exit code $LASTEXITCODE" }
    $expected = (Get-NormalizedText 'TESTS-OK').TrimEnd("`n")
    $actual   = (Get-NormalizedText 'TESTS-OUT').TrimEnd("`n")
    if ($expected -eq $actual) {
        Write-Host 'PASSED' -ForegroundColor Green
    } else {
        Write-Host 'FAILED' -ForegroundColor Red
        Compare-Object ($expected -split "`n") ($actual -split "`n") |
            Format-Table -AutoSize | Out-String | Write-Host
        exit 1
    }

    if (Test-Path -LiteralPath 'PHC-TEST-OK-SHA256') {
        Write-Host 'Running PHC tests'
        # Capture raw stdout (text mode -> CRLF), then verify the LF-normalized
        # SHA-256 against the known-good digest in PHC-TEST-OK-SHA256.
        & cmd /c ".\phc-test.exe > PHC-TEST-OUT 2>nul"
        if ($LASTEXITCODE -ne 0) { throw "phc-test.exe failed with exit code $LASTEXITCODE" }

        $bytes = [System.Text.Encoding]::ASCII.GetBytes((Get-NormalizedText 'PHC-TEST-OUT'))
        $sha = [System.Security.Cryptography.SHA256]::Create()
        try {
            $got = -join ($sha.ComputeHash($bytes) | ForEach-Object { $_.ToString('x2') })
        } finally {
            $sha.Dispose()
        }
        $expectedHash = ((Get-Content -Raw 'PHC-TEST-OK-SHA256').Trim() -split '\s+')[0].ToLower()
        if ($got -eq $expectedHash) {
            Write-Host 'PHC PASSED' -ForegroundColor Green
        } else {
            Write-Host "PHC FAILED (got $got, expected $expectedHash)" -ForegroundColor Red
            exit 1
        }
    }
}

function Invoke-Clean {
    $patterns = @('*.obj', 'tests.exe', 'phc-test.exe', 'TESTS-OUT', 'PHC-TEST-OUT',
                  '*.ilk', '*.pdb')
    foreach ($p in $patterns) {
        Get-ChildItem -LiteralPath $PSScriptRoot -Filter $p -ErrorAction SilentlyContinue |
            Remove-Item -Force -ErrorAction SilentlyContinue
    }
    Write-Host 'Cleaned build artifacts.'
}

# --- Dispatch ---------------------------------------------------------------

switch ($Target) {
    'clean' { Invoke-Clean; break }
    default {
        Import-VcEnvironment
        switch ($Target) {
            'all'       { Build-Tests; Build-PhcTest }
            'tests'     { Build-Tests }
            'phc-test'  { Build-PhcTest }
            'check'     { Invoke-Check }
            'ref'       { Build-Tests -Core $OBJS_CORE_REF; Build-PhcTest -Core $OBJS_CORE_REF }
            'check-ref' { Invoke-Check -Core $OBJS_CORE_REF }
        }
    }
}
