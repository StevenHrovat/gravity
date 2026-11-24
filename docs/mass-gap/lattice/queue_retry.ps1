# After the strong-coupling scan: the runs that stopped with CUDA out of memory, rerun with identical commands and seeds, each retried
# up to 3 times if it fails on GPU memory. Cause of the failures (2026-11-21, 10:00-10:40): GPU memory transiently exhausted by
# something outside these jobs (not identified; the bootstrap workers did not use the GPU, an earlier attribution was wrong).
#   pwsh -File queue_retry.ps1
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
while (-not ((Test-Path runs-gpu/queue.log) -and (Select-String -Path runs-gpu/queue.log -Pattern "STRONG DONE" -Quiet))) { Start-Sleep 60 }
$py = (Get-Command py).Source
function RunRetry([string]$name, [string[]]$a) {
    for ($i = 1; $i -le 3; $i++) {
        $t = Get-Date
        & $py -W ignore @a *> "runs-gpu/$name.log"
        $code = $LASTEXITCODE
        "$name (rerun, attempt $i) exit $code minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content runs-gpu/queue.log
        if ($code -eq 0) { return }
        if (-not (Select-String -Path "runs-gpu/$name.log" -Pattern "OUT_OF_MEMORY" -Quiet)) { return }
        Start-Sleep 120
    }
}
RunRetry vortex_b2.4_L16 @("vortex.py", "2.4", "16", "100", "20", "500", "402", "runs-gpu/vortex_b2.4_L16.npz", "4", "300")
RunRetry luscher_L6 @("run_su2_gpu.py", "2.3", "6", "16", "500", "2000", "606", "runs-gpu/luscher_b2.3_L6.npz", "3", "2", "10", "2,6,12,20")
RunRetry luscher_L14 @("run_su2_gpu.py", "2.3", "14", "16", "500", "2000", "614", "runs-gpu/luscher_b2.3_L14.npz", "3", "2", "10", "2,6,12,20")
"RETRY DONE" | Add-Content runs-gpu/queue.log
