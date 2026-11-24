# The pre-registered GPU runs of 2026-11-21, in order (PREREG-TTL.md, PREREG-VORTEX.md). Run from this folder with PowerShell:
#   pwsh -File queue_gpu.ps1
# Each run writes runs-gpu/<name>.npz (checkpointed) and runs-gpu/<name>.log; a line per finished run goes to runs-gpu/queue.log.
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
New-Item -ItemType Directory -Force runs-gpu | Out-Null
$py = (Get-Command py).Source
function Wait-Free([string]$pattern) {
    while (Get-CimInstance Win32_Process -Filter "Name like 'python%'" | Where-Object { $_.CommandLine -match $pattern }) { Start-Sleep 30 }
}
function Run([string]$name, [string[]]$a) {
    $t = Get-Date
    & $py -W ignore @a *> "runs-gpu/$name.log"
    "$name exit $LASTEXITCODE minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content runs-gpu/queue.log
}
Wait-Free 'run_su2_gpu\.py 2\.5 20 20 500 1000 252'   # the thread C box-size diagnostic finishes first
$lv = "2,6,12,20,32"
Run ttl_b2.3_L12 @("run_su2_gpu.py", "2.3", "12", "12", "500", "1000", "301", "runs-gpu/ttl_b2.3_L12.npz", "3", "2", "10", $lv)
Run ttl_b2.4_L16 @("run_su2_gpu.py", "2.4", "16", "16", "500", "1000", "302", "runs-gpu/ttl_b2.4_L16.npz", "3", "2", "10", $lv)
Run ttl_b2.5_L20 @("run_su2_gpu.py", "2.5", "20", "20", "500", "1000", "303", "runs-gpu/ttl_b2.5_L20.npz", "3", "2", "10", $lv)
Run ttl_b2.6_L28 @("run_su2_gpu.py", "2.6", "28", "28", "500", "800", "304", "runs-gpu/ttl_b2.6_L28.npz", "3", "2", "4", $lv)
Run ttl_b2.7_L32 @("run_su2_gpu.py", "2.7", "32", "32", "500", "600", "305", "runs-gpu/ttl_b2.7_L32.npz", "3", "2", "4", $lv)
Run vortex_b2.3_L12 @("vortex.py", "2.3", "12", "100", "20", "500", "401", "runs-gpu/vortex_b2.3_L12.npz", "4", "300")
Run vortex_b2.4_L16 @("vortex.py", "2.4", "16", "100", "20", "500", "402", "runs-gpu/vortex_b2.4_L16.npz", "4", "300")
"ALL DONE" | Add-Content runs-gpu/queue.log
