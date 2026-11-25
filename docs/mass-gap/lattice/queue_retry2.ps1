# The pre-registered strong-coupling scan (PREREG-STRONG.md), rerun with identical commands and seeds after queue_retry.ps1, each retried
# up to 3 times on CUDA out of memory. The first attempt (10:46-10:52) failed on all four beta with transient GPU memory exhaustion
# from outside these jobs (cause not identified).   pwsh -File queue_retry2.ps1
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
while (-not ((Test-Path runs-gpu/queue.log) -and (Select-String -Path runs-gpu/queue.log -Pattern "RETRY DONE" -Quiet))) { Start-Sleep 60 }
$py = (Get-Command py).Source
foreach ($b in "1.7", "1.9", "2.1", "2.2") {
    $name = "strong_b$b"
    for ($i = 1; $i -le 3; $i++) {
        $t = Get-Date
        & $py -W ignore run_su2_gpu.py $b 8 8 300 3000 (700 + [int]([double]$b * 10)) "runs-gpu/$name.npz" 3 2 10 "0,1,2,4" *> "runs-gpu/$name.log"
        $code = $LASTEXITCODE
        "$name (rerun, attempt $i) exit $code minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content runs-gpu/queue.log
        if ($code -eq 0) { break }
        if (-not (Select-String -Path "runs-gpu/$name.log" -Pattern "OUT_OF_MEMORY" -Quiet)) { break }
        Start-Sleep 120
    }
}
"STRONG RETRY DONE" | Add-Content runs-gpu/queue.log
