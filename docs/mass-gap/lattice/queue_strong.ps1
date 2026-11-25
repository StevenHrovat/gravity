# The pre-registered strong-coupling scan (PREREG-STRONG.md), started after the Luescher runs have finished.
#   pwsh -File queue_strong.ps1
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
while (-not ((Test-Path runs-gpu/queue.log) -and (Select-String -Path runs-gpu/queue.log -Pattern "LUSCHER DONE" -Quiet))) { Start-Sleep 60 }
$py = (Get-Command py).Source
foreach ($b in "1.7", "1.9", "2.1", "2.2") {
    $t = Get-Date
    & $py -W ignore run_su2_gpu.py $b 8 8 300 3000 (700 + [int]([double]$b * 10)) "runs-gpu/strong_b$b.npz" 3 2 10 "0,1,2,4" *> "runs-gpu/strong_b$b.log"
    "strong_b$b exit $LASTEXITCODE minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content runs-gpu/queue.log
}
"STRONG DONE" | Add-Content runs-gpu/queue.log
