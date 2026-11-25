# Leg C addendum (r3-blocked), added 2026-11-21 after the round-3 review, before any GPU data (PREREG.md "Changes before data").
# Runs blocked.py's PLAN_ADDENDUM after the main queue (queue_blocked_gpu.ps1, already started; it is not changed): a second Coulomb
# beta for the photon gate, and a coarse-volume check of SU(2) at beta 2.3. Then the final analysis over all runs.
# To be started by the coordinating session (any time; it waits for "BLOCKED DONE").    pwsh -File queue_blocked_gpu_addendum.ps1
# Estimated GPU time: about 35 min (+- 50 %).
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py).Source
$out = "runs-gpu"
New-Item -ItemType Directory -Force $out | Out-Null
$qlog = "$out/queue_blocked.log"
"ADDENDUM QUEUE START (waiting for BLOCKED DONE) $(Get-Date -Format s)" | Add-Content $qlog
while (-not ((Test-Path $qlog) -and (Select-String -Path $qlog -Pattern "^(BLOCKED DONE|SELFTEST FAILED|PHOTON GATE FAILED)" -Quiet))) { Start-Sleep 60 }
if (Select-String -Path $qlog -Pattern "^(SELFTEST FAILED|PHOTON GATE FAILED)" -Quiet) {
    "ADDENDUM not run: the main queue stopped at a gate $(Get-Date -Format s)" | Add-Content $qlog
    exit 0
}
# use the same GPU code path the main queue's selftest settled on (array code if the fused kernel failed there)
if (Select-String -Path $qlog -Pattern "selftest --gpu OK \(BLOCKED_FUSED=0\)" -Quiet) { $env:BLOCKED_FUSED = "0" }

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
# group, beta, N, blocks, fracs, n_therm, n_meas, chains, every, hot, gf_tmax, seed  (= blocked.PLAN_ADDENDUM)
$jobs = @(
    @("u1", "1.3", "36", "6,9,12", "0,0.25,0.5", "200", "80", "4", "4", $false, "0", "3107"),
    @("su2", "2.3", "24", "6,8", "0,0.25,0.5", "200", "80", "4", "4", $false, "0", "3108")
)
foreach ($j in $jobs) {
    $g, $b, $n, $bl, $fr, $th, $nm, $ch, $ev, $hot, $gf, $seed = $j
    $name = "${g}_b${b}_N${n}"
    if ((Test-Path "$out/$name.npz") -and (Select-String -Path $qlog -Pattern "^$name \(attempt \d\) exit 0" -Quiet)) { continue }
    $a = @("run", $g, $b, $n, $bl, $fr, $th, $nm, $seed, "$out/$name.npz", "--chains", $ch, "--every", $ev, "--gf-tmax", $gf)
    if ($hot) { $a += "--hot" }
    RunGpu $name $a
}
& $py -W ignore analyse_blocked.py "$out/*.npz" --out "$out/blocked_summary.json" *> "$out/analysis.log"
"BLOCKED ADDENDUM DONE $(Get-Date -Format s)" | Add-Content $qlog
