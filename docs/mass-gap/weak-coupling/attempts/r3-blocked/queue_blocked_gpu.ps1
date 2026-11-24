# Leg C (round 3, attempt 4, r3-blocked): the blocked-action "click" test on the GPU. Pre-registered in PREREG.md (this folder).
# To be started by the coordinating session after Leg B; never by an attempt.      pwsh -File queue_blocked_gpu.ps1
# Waits until Leg B's queue has logged "BOUNDARY DONE" and no boundary.py run is left; then:
#   1. selftest --gpu (fused quaternion kernel; if it fails, once more with the array-code path BLOCKED_FUSED=0; if that fails: stop)
#   2. bench (GPU timings and the projected total for the plan, in bench.log)
#   3. the photon control (U(1), beta 1.1) and its gate: if the primary blocking (f = 0.5) puts the photon inside any window, stop
#   4. SU(2) beta 2.3, the Z2 and confined-U(1) controls, SU(2) beta 2.4; 5. the final analysis.
# The job list is blocked.py's PLAN (same order, arguments and seeds); change both together, and PREREG.md first.
# Estimated GPU time: about 3.7 h (+- 50 %); see PREREG.md "Runs". Peak GPU memory about 4 GB (SU(2), 36^4, 4 chains).
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py).Source
$out = "runs-gpu"
New-Item -ItemType Directory -Force $out | Out-Null
$qlog = "$out/queue_blocked.log"
$legB = "../../../lattice/runs-gpu/boundary/queue_boundary.log"
"QUEUE START (waiting for Leg B) $(Get-Date -Format s)" | Add-Content $qlog
while (-not ((Test-Path $legB) -and (Select-String -Path $legB -Pattern "BOUNDARY DONE" -Quiet))) { Start-Sleep 60 }
while (Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match 'boundary\.py run ' }) { Start-Sleep 30 }
"Leg B done; starting $(Get-Date -Format s)" | Add-Content $qlog

# 1. GPU selftest (gate)
& $py -W ignore blocked.py selftest --gpu *> "$out/selftest_gpu.log"
if ($LASTEXITCODE -ne 0) {
    "selftest --gpu FAILED with the fused kernel; retrying with BLOCKED_FUSED=0" | Add-Content $qlog
    $env:BLOCKED_FUSED = "0"
    & $py -W ignore blocked.py selftest --gpu *> "$out/selftest_gpu_array.log"
    if ($LASTEXITCODE -ne 0) { "SELFTEST FAILED on both paths: queue stopped $(Get-Date -Format s)" | Add-Content $qlog; exit 1 }
}
"selftest --gpu OK (BLOCKED_FUSED=$($env:BLOCKED_FUSED))" | Add-Content $qlog

# 2. timings and projection
& $py -W ignore blocked.py bench --N 36 --chains 4 *> "$out/bench.log"
(Select-String -Path "$out/bench.log" -Pattern "PROJECTED TOTAL").Line | Add-Content $qlog

function RunGpu([string]$name, [string[]]$a) {
    for ($i = 1; $i -le 3; $i++) {
        $t = Get-Date
        & $py -W ignore blocked.py @a *> "$out/$name.log"
        $code = $LASTEXITCODE
        "$name (attempt $i) exit $code minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content $qlog
        if ($code -eq 0) { return }
        if (-not (Select-String -Path "$out/$name.log" -Pattern "OUT_OF_MEMORY|OutOfMemory" -Quiet)) { return }
        Start-Sleep 120
    }
}
# group, beta, N, blocks, fracs, n_therm, n_meas, chains, every, hot, gf_tmax, seed  (= blocked.PLAN)
$jobs = @(
    @("u1", "1.1", "36", "6,9,12", "0,0.25,0.5", "200", "80", "4", "4", $false, "0", "3101"),
    @("su2", "2.3", "36", "6,9,12", "0,0.25,0.5", "200", "80", "4", "4", $false, "10.125", "3102"),
    @("z2", "0.6", "36", "6,9,12", "0", "200", "80", "4", "4", $false, "0", "3103"),
    @("u1", "0.9", "36", "6,9,12", "0,0.25,0.5", "200", "80", "4", "4", $true, "0", "3104"),
    @("z2", "0.3", "36", "6,9,12", "0", "200", "80", "4", "4", $true, "0", "3105"),
    @("su2", "2.4", "36", "6,9,12", "0,0.25,0.5", "200", "80", "4", "4", $false, "0", "3106")
)
foreach ($j in $jobs) {
    $g, $b, $n, $bl, $fr, $th, $nm, $ch, $ev, $hot, $gf, $seed = $j
    $name = "${g}_b${b}_N${n}"
    if ((Test-Path "$out/$name.npz") -and (Select-String -Path $qlog -Pattern "^$name \(attempt \d\) exit 0" -Quiet)) { continue }
    $a = @("run", $g, $b, $n, $bl, $fr, $th, $nm, $seed, "$out/$name.npz", "--chains", $ch, "--every", $ev, "--gf-tmax", $gf)
    if ($hot) { $a += "--hot" }
    RunGpu $name $a
    if ($name -eq "u1_b1.1_N36") {
        # 3. photon gate on the primary blocking
        & $py -W ignore analyse_blocked.py "$out/u1_b1.1_N36.npz" --gate-photon *> "$out/photon_gate.log"
        if (Select-String -Path "$out/photon_gate.log" -Pattern "PHOTON GATE PASSED" -Quiet) {
            "PHOTON GATE PASSED $(Get-Date -Format s)" | Add-Content $qlog
        } else {
            "PHOTON GATE FAILED: queue stopped before SU(2) $(Get-Date -Format s)" | Add-Content $qlog
            exit 0
        }
    }
}
# 5. final analysis
& $py -W ignore analyse_blocked.py "$out/*.npz" --out "$out/blocked_summary.json" *> "$out/analysis.log"
"BLOCKED DONE $(Get-Date -Format s)" | Add-Content $qlog
