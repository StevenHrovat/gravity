# Rerun of the pre-registered vortex run at beta 2.4 (PREREG-VORTEX.md), identical command and seed. The first attempt stopped at
# configuration 87 of 100 with CUDA out of memory (another job's processes held GPU contexts); its output is kept as
# runs-gpu/vortex_b2.4_L16_oom87.npz/.log. Starts after the strong-coupling scan.   pwsh -File queue_vortex_rerun.ps1
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
while (-not ((Test-Path runs-gpu/queue.log) -and (Select-String -Path runs-gpu/queue.log -Pattern "STRONG DONE" -Quiet))) { Start-Sleep 60 }
$py = (Get-Command py).Source
$t = Get-Date
& $py -W ignore vortex.py 2.4 16 100 20 500 402 runs-gpu/vortex_b2.4_L16.npz 4 300 *> runs-gpu/vortex_b2.4_L16.log
"vortex_b2.4_L16 (rerun) exit $LASTEXITCODE minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content runs-gpu/queue.log
"VORTEX RERUN DONE" | Add-Content runs-gpu/queue.log
