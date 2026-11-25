# The pre-registered flux-tube runs (PREREG-LUSCHER.md), started after the main GPU queue (../lattice/queue_gpu.ps1) has finished.
#   pwsh -File queue_luscher.ps1
$ErrorActionPreference = "Continue"
$lat = Join-Path $PSScriptRoot "..\lattice"
Set-Location $lat
while (-not ((Test-Path runs-gpu/queue.log) -and (Select-String -Path runs-gpu/queue.log -Pattern "ALL DONE" -Quiet))) { Start-Sleep 60 }
$py = (Get-Command py).Source
foreach ($L in 6, 8, 10, 12, 14) {
    $t = Get-Date
    & $py -W ignore run_su2_gpu.py 2.3 $L 16 500 2000 (600 + $L) "runs-gpu/luscher_b2.3_L$L.npz" 3 2 10 "2,6,12,20" *> "runs-gpu/luscher_L$L.log"
    "luscher_L$L exit $LASTEXITCODE minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content runs-gpu/queue.log
}
"LUSCHER DONE" | Add-Content runs-gpu/queue.log
