# Cycle 3, workstream 2 (c3b-refit): the real click test, refit with the good blocking, on the GPU. Pre-registered in PREREG.md.
# To be started by the coordinating session; never by a workstream.      pwsh -File queue_refit_gpu.ps1
# Waits until the act-number queue (../../attempts/r4-actnumber/queue_actnumber_gpu.ps1) has finished: its log
# runs-gpu/queue_actnumber.log has the final line "ACTNUMBER DONE ..." (or one of its early-stop lines "SELFTEST FAILED ..." /
# "PHOTON GATE FAILED ..."; or the coordinator's stop line "QUEUE STOPPED by the coordinator after the bench", 2026-11-22), and no actnumber.py, blocked.py or boundary.py run is alive (checked twice, 3 minutes apart). Then:
#   1. selftest --gpu (fused kernel; if it fails, the array-code path with BLOCKED_FUSED=0; if that fails too: stop)
#   2. bench (timings at 48^4 and the projected total, copied into the queue log)
#   3. the photon gate (U(1), beta 1.1, 48^4, b = 4, 8, 16) and its decision: if it fails, stop before SU(2)
#   4. the deconfined Z2 gate run, then the SU(2) runs (beta 2.3, 2.5, 2.4), in goodblock.PLAN's order
#   5. the final analysis (runs-gpu/analysis.log, runs-gpu/refit_summary.json)
# Estimated GPU time: about 2.8 h (+- 50 %); see PREREG.md "Runs". Peak GPU memory about 4.5 GB (2 chains of 48^4).
# Resumable: a run whose .npz exists and whose "exit 0" line is in the queue log is skipped on a restart.
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py).Source
$out = "runs-gpu"
New-Item -ItemType Directory -Force $out | Out-Null
$qlog = "$out/queue_refit.log"
$act = "../../attempts/r4-actnumber/runs-gpu/queue_actnumber.log"
"QUEUE START (waiting for the act-number queue) $(Get-Date -Format s)" | Add-Content $qlog

function ActDone {
    if (-not (Test-Path $act)) { return $false }
    return [bool](Select-String -Path $act -Pattern "^(ACTNUMBER DONE|SELFTEST FAILED|PHOTON GATE FAILED|QUEUE STOPPED by the coordinator after the bench)" -Quiet)
}
function OthersRunning {
    return [bool](Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match '(actnumber|blocked|boundary)\.py' -and $_.CommandLine -notmatch 'goodblock' })
}
while ($true) {
    while (-not (ActDone)) { Start-Sleep 60 }
    while (OthersRunning) { Start-Sleep 30 }
    Start-Sleep 180
    if ((ActDone) -and -not (OthersRunning)) { break }
}
"act-number queue done, GPU free of actnumber.py/blocked.py/boundary.py; starting $(Get-Date -Format s)" | Add-Content $qlog

# 1. GPU selftest (gate)
& $py -W ignore goodblock.py selftest --gpu *> "$out/selftest_gpu.log"
if ($LASTEXITCODE -ne 0) {
    "selftest --gpu FAILED with the fused kernel; retrying with the array-code path (BLOCKED_FUSED=0)" | Add-Content $qlog
    $env:BLOCKED_FUSED = "0"
    & $py -W ignore goodblock.py selftest --gpu *> "$out/selftest_gpu_array.log"
    if ($LASTEXITCODE -ne 0) { "SELFTEST FAILED on both paths: queue stopped $(Get-Date -Format s)" | Add-Content $qlog; exit 1 }
}
"selftest --gpu OK (BLOCKED_FUSED=$env:BLOCKED_FUSED)" | Add-Content $qlog

# 2. timings and projection
& $py -W ignore goodblock.py bench *> "$out/bench.log"
(Select-String -Path "$out/bench.log" -Pattern "PROJECTED TOTAL").Line | Add-Content $qlog

function RunPlan([string]$name) {
    if ((Test-Path "$out/$name.npz") -and (Select-String -Path $qlog -Pattern "^$name \(attempt \d\) exit 0" -Quiet)) { return }
    for ($i = 1; $i -le 3; $i++) {
        $t = Get-Date
        & $py -W ignore goodblock.py runplan $name $out *> "$out/$name.log"
        $code = $LASTEXITCODE
        "$name (attempt $i) exit $code minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content $qlog
        if ($code -eq 0) { return }
        if (-not (Select-String -Path "$out/$name.log" -Pattern "OUT_OF_MEMORY|OutOfMemory" -Quiet)) { return }
        Start-Sleep 120
    }
}

$names = & $py goodblock.py plannames
# 3. photon gate
RunPlan "u1_b1.1_N48"
& $py -W ignore analyse_refit.py "$out/u1_b1.1_N48.npz" --photon-gate *> "$out/photon_gate.log"
if (Select-String -Path "$out/photon_gate.log" -Pattern "PHOTON GATE PASSED" -Quiet) {
    "PHOTON GATE PASSED $(Get-Date -Format s)" | Add-Content $qlog
} else {
    "PHOTON GATE FAILED: queue stopped before SU(2) $(Get-Date -Format s)" | Add-Content $qlog
    & $py -W ignore analyse_refit.py "$out/*.npz" --out "$out/refit_summary.json" *> "$out/analysis.log"
    exit 0
}
# 4. the rest of the plan, in order
foreach ($n in $names) {
    if ($n -eq "u1_b1.1_N48") { continue }
    RunPlan $n
}
# 5. final analysis
& $py -W ignore analyse_refit.py "$out/*.npz" --out "$out/refit_summary.json" *> "$out/analysis.log"
"REFIT DONE $(Get-Date -Format s)" | Add-Content $qlog
