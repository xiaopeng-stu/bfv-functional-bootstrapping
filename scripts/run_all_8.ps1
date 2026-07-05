# run_all_8.ps1
# Run the eight paper-style benchmark commands sequentially and save one log per case.

$ErrorActionPreference = "Continue"
$StopOnError = $false
Set-Location (Join-Path $PSScriptRoot "..")

$TimeTag = Get-Date -Format "yyyyMMdd_HHmmss"
$LogDir = Join-Path (Get-Location) "logs\run_$TimeTag"
New-Item -ItemType Directory -Force -Path $LogDir | Out-Null
$SummaryFile = Join-Path $LogDir "summary.txt"
"Start time: $(Get-Date)" | Out-File -FilePath $SummaryFile -Encoding utf8
"Working directory: $(Get-Location)" | Out-File -FilePath $SummaryFile -Encoding utf8 -Append
"" | Out-File -FilePath $SummaryFile -Encoding utf8 -Append

$Cases = @(
    @{
        Name = "01_9bit_m1"
        Args = @("run", ".", "-N", "32768", "-m", "1", "-degree", "65536", "-T", "65537", "-p", "512", "-func", "random", "-logq", "36,34x18,30", "-logp", "34,34,34,34", "-lwe-n", "2048", "-lwe-h", "512", "-run", "100")
    },
    @{
        Name = "02_9bit_m128"
        Args = @("run", ".", "-N", "32768", "-m", "128", "-degree", "65536", "-T", "65537", "-p", "512", "-func", "random", "-logq", "36,34,34x18,30", "-logp", "34,34,34,34", "-lwe-n", "2048", "-lwe-h", "512", "-run", "100")
    },
    @{
        Name = "03_12bit_m1"
        Args = @("run", ".", "-N", "65536", "-m", "1", "-degree", "1048575", "-T", "786433", "-p", "4096", "-func", "random", "-logq", "39,38x22,38", "-logp", "38,38,38,38,38", "-lwe-n", "2048", "-lwe-h", "512", "-run", "100")
    },
    @{
        Name = "04_12bit_m64"
        Args = @("run", ".", "-N", "65536", "-m", "64", "-degree", "1048575", "-T", "786433", "-p", "4096", "-func", "random", "-logq", "39,38,38x22,38", "-logp", "38,38,38,38,38", "-lwe-n", "2048", "-lwe-h", "512", "-run", "100")
    },
    @{
        Name = "05_14bit_m1"
        Args = @("run", ".", "-N", "65536", "-m", "1", "-degree", "4194303", "-T", "2752513", "-p", "16384", "-func", "random", "-logq", "42,40x24,40", "-logp", "40,40,40,40,40", "-lwe-n", "2048", "-lwe-h", "512", "-run", "100")
    },
    @{
        Name = "06_14bit_m32"
        Args = @("run", ".", "-N", "65536", "-m", "32", "-degree", "4194303", "-T", "2752513", "-p", "16384", "-func", "random", "-logq", "42,40,40x24,40", "-logp", "40,40,40,40,40", "-lwe-n", "2048", "-lwe-h", "512", "-run", "100")
    },
    @{
        Name = "07_16bit_m1"
        Args = @("run", ".", "-N", "65536", "-m", "1", "-degree", "8388607", "-T", "8257537", "-p", "65536", "-func", "random", "-logq", "45,43x25,40", "-logp", "40,40,40,40,40,40", "-lwe-n", "2048", "-lwe-h", "512", "-run", "100")
    },
    @{
        Name = "08_16bit_m16"
        Args = @("run", ".", "-N", "65536", "-m", "16", "-degree", "8388607", "-T", "8257537", "-p", "65536", "-func", "random", "-logq", "45,45,45x25,40", "-logp", "40,40,40,40,40,40", "-lwe-n", "2048", "-lwe-h", "512", "-run", "100")
    }
)

for ($i = 0; $i -lt $Cases.Count; $i++) {
    $Case = $Cases[$i]
    $Index = $i + 1
    $LogFile = Join-Path $LogDir ($Case.Name + ".log")
    $CommandLine = "go " + ($Case.Args -join " ")

    Write-Host ""
    Write-Host "============================================================"
    Write-Host "Running case $Index/$($Cases.Count): $($Case.Name)"
    Write-Host "Log file: $LogFile"
    Write-Host "============================================================"

    "============================================================" | Out-File -FilePath $LogFile -Encoding utf8
    "Case: $($Case.Name)" | Out-File -FilePath $LogFile -Encoding utf8 -Append
    "Start time: $(Get-Date)" | Out-File -FilePath $LogFile -Encoding utf8 -Append
    "Command: $CommandLine" | Out-File -FilePath $LogFile -Encoding utf8 -Append
    "============================================================" | Out-File -FilePath $LogFile -Encoding utf8 -Append
    "" | Out-File -FilePath $LogFile -Encoding utf8 -Append

    $Start = Get-Date
    & go @($Case.Args) *>> $LogFile
    $ExitCode = $LASTEXITCODE
    $End = Get-Date
    $Elapsed = $End - $Start

    "" | Out-File -FilePath $LogFile -Encoding utf8 -Append
    "============================================================" | Out-File -FilePath $LogFile -Encoding utf8 -Append
    "End time: $End" | Out-File -FilePath $LogFile -Encoding utf8 -Append
    "Elapsed: $Elapsed" | Out-File -FilePath $LogFile -Encoding utf8 -Append
    "Exit code: $ExitCode" | Out-File -FilePath $LogFile -Encoding utf8 -Append
    "============================================================" | Out-File -FilePath $LogFile -Encoding utf8 -Append

    $SummaryLine = "{0}/{1} {2}: exit={3}, elapsed={4}" -f $Index, $Cases.Count, $Case.Name, $ExitCode, $Elapsed
    $SummaryLine | Tee-Object -FilePath $SummaryFile -Append

    if (($ExitCode -ne 0) -and $StopOnError) {
        "Stopped because $($Case.Name) failed." | Tee-Object -FilePath $SummaryFile -Append
        exit $ExitCode
    }
}

"" | Out-File -FilePath $SummaryFile -Encoding utf8 -Append
"Finish time: $(Get-Date)" | Out-File -FilePath $SummaryFile -Encoding utf8 -Append
"All cases finished." | Out-File -FilePath $SummaryFile -Encoding utf8 -Append

Write-Host ""
Write-Host "All cases finished."
Write-Host "Summary file:"
Write-Host $SummaryFile
Write-Host "Logs directory:"
Write-Host $LogDir
Write-Host ""
Write-Host "To clean and parse this log directory:"
Write-Host "python scripts\clean_powershell_logs.py $LogDir data-regenerated.txt"
Write-Host "python scripts\parse_summary.py data-regenerated.txt summary-regenerated.csv"
