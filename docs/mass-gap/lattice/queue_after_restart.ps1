# The GPU runs tabled on 2026-11-21 (11:20) before the laptop restart, restarted afterwards with identical commands and seeds, each
# retried up to 3 times on CUDA out of memory: vortex beta 2.4 (PREREG-VORTEX.md, PREREG-VORTEX-SIGMA.md), Luescher L = 6 and 14
# (../zeta/PREREG-LUSCHER.md), the strong-coupling scan (PREREG-STRONG.md).   pwsh -File queue_after_restart.ps1
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py).Source
function RunRetry([string]$name, [string[]]$a) {
    for ($i = 1; $i -le 3; $i++) {
        $t = Get-Date
        & $py -W ignore @a *> "runs-gpu/$name.log"
        $code = $LASTEXITCODE
        "$name (after restart, attempt $i) exit $code minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content runs-gpu/queue.log
        if ($code -eq 0) { return }
        if (-not (Select-String -Path "runs-gpu/$name.log" -Pattern "OUT_OF_MEMORY" -Quiet)) { return }
        Start-Sleep 120
    }
}
"RESTARTED $(Get-Date -Format s)" | Add-Content runs-gpu/queue.log
foreach ($b in "1.7", "1.9", "2.1", "2.2") {
    RunRetry "strong_b$b" @("run_su2_gpu.py", $b, "8", "8", "300", "3000", "$(700 + [int]([double]$b * 10))", "runs-gpu/strong_b$b.npz", "3", "2", "10", "0,1,2,4")
}
RunRetry luscher_L6 @("run_su2_gpu.py", "2.3", "6", "16", "500", "2000", "606", "runs-gpu/luscher_b2.3_L6.npz", "3", "2", "10", "2,6,12,20")
RunRetry luscher_L14 @("run_su2_gpu.py", "2.3", "14", "16", "500", "2000", "614", "runs-gpu/luscher_b2.3_L14.npz", "3", "2", "10", "2,6,12,20")
RunRetry vortex_b2.4_L16 @("vortex.py", "2.4", "16", "100", "20", "500", "402", "runs-gpu/vortex_b2.4_L16.npz", "4", "300")
"AFTER RESTART DONE" | Add-Content runs-gpu/queue.log
