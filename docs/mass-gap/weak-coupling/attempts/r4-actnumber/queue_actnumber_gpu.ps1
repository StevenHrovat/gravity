# Round 4, r4-actnumber: the act number z(L) = E_e(L) L of SU(2) in a twisted box, on the GPU. Pre-registered in PREREG.md (this folder).
# To be started by the coordinating session; never by an attempt.      pwsh -File queue_actnumber_gpu.ps1
# Waits until Leg C (r3-blocked) is finished: its queue log has "ADDENDUM DONE" (the addendum's last line is "BLOCKED ADDENDUM DONE") or
# "ADDENDUM not run" (the addendum stopped at a gate of the main queue), or "BLOCKED DONE" with no addendum queue process alive; and no
# blocked.py or boundary.py run is left (checked twice, 3 minutes apart). Then:
#   1. selftest --gpu (fused kernel + sheet fix-up; if it fails, the array-code path alone: selftest --gpu --no-fused; if that fails: stop)
#   2. bench (GPU timings and the projected total of the plan, in bench.log; the projection is copied into the queue log)
#   3. the photon control (U(1), beta 1.1, L = 4, 6, 8, 10) and its gate: if it fails, stop before SU(2)
#   4. every other entry of actnumber.PLAN, in its order (core first; the reported extras last); 5. the final analysis.
# The job list is actnumber.py's PLAN (names, arguments, seeds): `py actnumber.py plannames`, `py actnumber.py runplan NAME DIR`.
# Estimated GPU time: about 4.8 h (+- 50 %), core runs 4.2 h; see PREREG.md "Runs". Peak GPU memory well below 1 GB.
# Optional: -AddendumW also runs actnumber.PLAN_W after the plan (r4-conjw's four-move split, about 1.3 h more); coordinator's decision.
# Resumable: a run whose .npz exists and whose "exit 0" line is in the queue log is skipped on a restart.
param([switch]$AddendumW)
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py).Source
$out = "runs-gpu"
New-Item -ItemType Directory -Force $out | Out-Null
$qlog = "$out/queue_actnumber.log"
$legC = "../r3-blocked/runs-gpu/queue_blocked.log"
"QUEUE START (waiting for Leg C) $(Get-Date -Format s)" | Add-Content $qlog

function LegCDone {
    if (-not (Test-Path $legC)) { return $false }
    if (Select-String -Path $legC -Pattern "ADDENDUM DONE|^ADDENDUM not run" -Quiet) { return $true }
    if (Select-String -Path $legC -Pattern "^BLOCKED DONE" -Quiet) {
        $addq = Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match 'queue_blocked_gpu_addendum' }
        if (-not $addq) { return $true }
    }
    return $false
}
function OthersRunning {
    return [bool](Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match '(blocked|boundary)\.py (run|couple)' })
}
while ($true) {
    while (-not (LegCDone)) { Start-Sleep 60 }
    while (OthersRunning) { Start-Sleep 30 }
    Start-Sleep 180
    if ((LegCDone) -and -not (OthersRunning)) { break }
}
"Leg C done, GPU free of blocked.py/boundary.py; starting $(Get-Date -Format s)" | Add-Content $qlog

# 1. GPU selftest (gate)
$path = "fused"
& $py -W ignore actnumber.py selftest --gpu *> "$out/selftest_gpu.log"
if ($LASTEXITCODE -ne 0) {
    "selftest --gpu FAILED with the fused path; retrying with the array-code path only" | Add-Content $qlog
    & $py -W ignore actnumber.py selftest --gpu --no-fused *> "$out/selftest_gpu_array.log"
    if ($LASTEXITCODE -ne 0) { "SELFTEST FAILED on both paths: queue stopped $(Get-Date -Format s)" | Add-Content $qlog; exit 1 }
    $path = "array"
}
"selftest --gpu OK (path=$path)" | Add-Content $qlog

# 2. timings and projection
if ($AddendumW) { & $py -W ignore actnumber.py bench --path $path --addendum *> "$out/bench.log" }
else { & $py -W ignore actnumber.py bench --path $path *> "$out/bench.log" }
(Select-String -Path "$out/bench.log" -Pattern "PROJECTED TOTAL").Line | Add-Content $qlog

function RunPlan([string]$name) {
    if ((Test-Path "$out/$name.npz") -and (Select-String -Path $qlog -Pattern "^$name \(attempt \d\) exit 0" -Quiet)) { return }
    for ($i = 1; $i -le 3; $i++) {
        $t = Get-Date
        & $py -W ignore actnumber.py runplan $name $out --path $path *> "$out/$name.log"
        $code = $LASTEXITCODE
        "$name (attempt $i) exit $code minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content $qlog
        if ($code -eq 0) { return }
        if (-not (Select-String -Path "$out/$name.log" -Pattern "OUT_OF_MEMORY|OutOfMemory" -Quiet)) { return }
        Start-Sleep 120
    }
}

$names = & $py actnumber.py plannames
# 3. photon gate
$gate = @("u1_b1.1_L4", "u1_b1.1_L6", "u1_b1.1_L8", "u1_b1.1_L10")
foreach ($n in $gate) { RunPlan $n }
& $py -W ignore analyse_actnumber.py ($gate | ForEach-Object { "$out/$_.npz" }) --photon-gate *> "$out/photon_gate.log"
if (Select-String -Path "$out/photon_gate.log" -Pattern "PHOTON GATE PASSED" -Quiet) {
    "PHOTON GATE PASSED $(Get-Date -Format s)" | Add-Content $qlog
} else {
    "PHOTON GATE FAILED: queue stopped before SU(2) $(Get-Date -Format s)" | Add-Content $qlog
    exit 0
}
# 4. the rest of the plan, in order
foreach ($n in $names) {
    if ($gate -contains $n) { continue }
    RunPlan $n
}
# 4b. optional four-move addendum
if ($AddendumW) {
    "ADDENDUM W START $(Get-Date -Format s)" | Add-Content $qlog
    foreach ($n in (& $py actnumber.py plannames --addendum)) { RunPlan $n }
}
# 5. final analysis
& $py -W ignore analyse_actnumber.py "$out/*.npz" --out "$out/actnumber_summary.json" *> "$out/analysis.log"
"ACTNUMBER DONE $(Get-Date -Format s)" | Add-Content $qlog
