# Boundary-influence instrument (Leg B), production plan of PREREG-BOUNDARY.md. DRAFT: do not start before the owner has reviewed the
# pre-registration.   pwsh -File queue_boundary.ps1
#
# 1. Waits until runs-gpu/queue.log contains "AFTER RESTART DONE" (the pre-registered queue started 2026-11-21 13:42).
# 2. Controls on the CPU, 8 jobs in parallel (GPU stays free): the photon test (U(1), beta 1.1 and 0.9) and the Ising-gauge test (Z2,
#    beta 0.6 and 0.3), then the photon-test gate: if the instrument cannot tell the Coulomb phase from the confined one, it stops here
#    ("PHOTON TEST FAILED"), because SU(2) numbers from it would say nothing about the gap.
# 3. SU(2) on the GPU, one job at a time, boxes of fixed physical size (ell * a * sqrt(sigma) = 2.8), coarse to fine, then a second
#    physical size (4.2) at beta 2.3 and 2.4; each job retried up to 3 times on CUDA out of memory.
# 4. Coupled-chain estimates of k_V(y) (BLUEPRINT-REDUCTION.md 5.1): U(1) and Z2 in phase 2 on the CPU; SU(2) on the CPU (6 jobs)
#    while phase 3 runs on the GPU (the coupled path is launch-bound array code, about 4 s per sweep on the GPU, no faster than a core).
# 5. The analysis: runs-gpu/boundary/boundary_summary.json and the printed tables in runs-gpu/boundary/analysis.log.
# Progress: runs-gpu/boundary/queue_boundary.log (one line per job with exit code and minutes).
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py).Source
$out = "runs-gpu/boundary"
New-Item -ItemType Directory -Force $out | Out-Null
$qlog = "$out/queue_boundary.log"

while (-not (Select-String -Path "runs-gpu/queue.log" -Pattern "AFTER RESTART DONE" -Quiet)) { Start-Sleep 60 }
"START $(Get-Date -Format s)" | Add-Content $qlog

function RunGpu([string]$name, [string[]]$a) {
    for ($i = 1; $i -le 3; $i++) {
        $t = Get-Date
        & $py -W ignore boundary.py @a *> "$out/$name.log"
        $code = $LASTEXITCODE
        "$name (gpu, attempt $i) exit $code minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content $qlog
        if ($code -eq 0) { return }
        if (-not (Select-String -Path "$out/$name.log" -Pattern "OUT_OF_MEMORY" -Quiet)) { return }
        Start-Sleep 120
    }
}

function RunCpuBatch([object[]]$jobs, [int]$parallel = 8) {
    # CPU jobs never see the GPU; at most $parallel at once; returns when all have finished
    $running = @()
    foreach ($j in $jobs) {
        while (@($running | Where-Object { -not $_.P.HasExited }).Count -ge $parallel) { Start-Sleep 20 }
        $env:CUDA_VISIBLE_DEVICES = "-1"
        $p = Start-Process -FilePath $py -ArgumentList (@("-W", "ignore", "boundary.py") + $j.A + @("--cpu")) -NoNewWindow -PassThru `
            -RedirectStandardOutput "$out/$($j.N).log" -RedirectStandardError "$out/$($j.N).err"
        Remove-Item Env:CUDA_VISIBLE_DEVICES
        $running += [pscustomobject]@{ N = $j.N; P = $p; T = Get-Date }
    }
    foreach ($r in $running) {
        $r.P.WaitForExit()
        "$($r.N) (cpu) exit $($r.P.ExitCode) minutes $([int]((Get-Date) - $r.T).TotalMinutes)" | Add-Content $qlog
    }
}

# ---- 2. controls (CPU) -------------------------------------------------------------------------------------------------------------
$cpu = @()
foreach ($b in "1.1", "0.9") {
    $s = [int]([double]$b * 10)
    foreach ($l in 6, 8, 12) {
        $n = @{ 6 = "1500"; 8 = "1200"; 12 = "800" }[$l]
        foreach ($bc in "calm", "flux") {
            $cpu += @{ N = "u1_b${b}_l${l}_$bc"; A = @("run", "u1", $b, "$l", $bc, "300", $n, "$(1000 + 100 * $s + $l)", "$out/u1_b${b}_l${l}_$bc.npz", "--chains", "4", "--smear", "4") }
        }
    }
    foreach ($l in 6, 8, 12) {
        $n = @{ 6 = "1500"; 8 = "1200"; 12 = "800" }[$l]
        $cpu += @{ N = "u1phi05_b${b}_l${l}_flux"; A = @("run", "u1", $b, "$l", "flux", "300", $n, "$(1500 + 100 * $s + $l)", "$out/u1phi05_b${b}_l${l}_flux.npz", "--chains", "4", "--smear", "4", "--phi", "0.5") }
    }
    foreach ($l in 4, 6, 8, 10) {
        $cpu += @{ N = "cpl_u1_b${b}_l$l"; A = @("couple", "u1", $b, "$l", "calm", "face", "200", "300", "$(3000 + 100 * $s + $l)", "$out/cpl_u1_b${b}_l$l.npz", "--pairs", "4", "--every", "1") }
    }
}
# Review addition (pre-registration header, decision 1): U(1) beta 0.8 at l = 12, reported only, not part of the gate.
foreach ($bc in "calm", "flux") {
    $cpu += @{ N = "u1_b0.8_l12_$bc"; A = @("run", "u1", "0.8", "12", $bc, "300", "800", "1812", "$out/u1_b0.8_l12_$bc.npz", "--chains", "4", "--smear", "4") }
}
$cpu += @{ N = "u1phi05_b0.8_l12_flux"; A = @("run", "u1", "0.8", "12", "flux", "300", "800", "2312", "$out/u1phi05_b0.8_l12_flux.npz", "--chains", "4", "--smear", "4", "--phi", "0.5") }
foreach ($b in "0.6", "0.3") {
    $s = [int]([double]$b * 10)
    foreach ($l in 6, 8, 12) {
        foreach ($bc in "calm", "twist") {
            $cpu += @{ N = "z2_b${b}_l${l}_$bc"; A = @("run", "z2", $b, "$l", $bc, "300", "1000", "$(2000 + 100 * $s + $l)", "$out/z2_b${b}_l${l}_$bc.npz", "--chains", "4", "--smear", "4") }
        }
    }
    foreach ($l in 4, 6, 8, 10) {
        $cpu += @{ N = "cpl_z2_b${b}_l${l}_twist"; A = @("couple", "z2", $b, "$l", "twist", "face", "200", "300", "$(4000 + 100 * $s + $l)", "$out/cpl_z2_b${b}_l${l}_twist.npz", "--pairs", "4", "--every", "1") }
    }
}
RunCpuBatch $cpu 8

& $py -W ignore analyse_boundary.py "$out/u1_*.npz" "$out/u1phi05_*.npz" "$out/z2_*.npz" "$out/cpl_u1_*.npz" "$out/cpl_z2_*.npz" --out "$out/controls_summary.json" --photon-gate *> "$out/controls_analysis.log"
if ($LASTEXITCODE -ne 0) {
    "PHOTON TEST FAILED or incomplete (analyse_boundary.py exit $LASTEXITCODE): SU(2) runs not started; see $out/controls_analysis.log" | Add-Content $qlog
    "BOUNDARY DONE (stopped at the photon gate)" | Add-Content $qlog
    exit 1
}
"PHOTON TEST PASSED $(Get-Date -Format s)" | Add-Content $qlog

# ---- 4 (started first, runs alongside 3): SU(2) coupled chains on the CPU, 6 at a time -------------------------------------------------
$cplJobs = @()
foreach ($r in @(@("2.3", @(4, 6, 8)), @("2.5", @(6, 8, 10)))) {
    $b = $r[0]
    foreach ($l in $r[1]) {
        $cplJobs += @{ N = "cpl_su2_b${b}_l$l"; A = @("couple", "su2", $b, "$l", "calm", "face", "200", "300", "$(5000 + $l)", "$out/cpl_su2_b${b}_l$l.npz", "--pairs", "4", "--every", "1") }
    }
}
$cplSeen = @()
$cplRunning = @()
function PumpCoupled {
    # start queued SU(2) coupled jobs while fewer than 6 run; log finished ones; called between GPU jobs and at the end
    foreach ($r in @($script:cplRunning | Where-Object { $_.P.HasExited -and ($script:cplSeen -notcontains $_.N) })) {
        "$($r.N) (cpu) exit $($r.P.ExitCode) minutes $([int]((Get-Date) - $r.T).TotalMinutes)" | Add-Content $qlog
        $script:cplSeen += $r.N
    }
    while ($script:cplJobs.Count -gt 0 -and @($script:cplRunning | Where-Object { -not $_.P.HasExited }).Count -lt 6) {
        $j = $script:cplJobs[0]
        $script:cplJobs = @($script:cplJobs | Select-Object -Skip 1)
        $env:CUDA_VISIBLE_DEVICES = "-1"
        $p = Start-Process -FilePath $py -ArgumentList (@("-W", "ignore", "boundary.py") + $j.A + @("--cpu")) -NoNewWindow -PassThru `
            -RedirectStandardOutput "$out/$($j.N).log" -RedirectStandardError "$out/$($j.N).err"
        Remove-Item Env:CUDA_VISIBLE_DEVICES
        $script:cplRunning += [pscustomobject]@{ N = $j.N; P = $p; T = Get-Date }
    }
}
PumpCoupled

# ---- 3. SU(2), fixed physical box size (GPU) ---------------------------------------------------------------------------------------
# beta, ell, chains, measurements
# beta, ell, chains, measurements, BCs; main series ell * a * sqrt(sigma) = 2.8, then a second physical size 4.2 at the two coarse betas
$su2 = @(
    @("2.3", "8", "16", "1000", "calm typical twist flux hot"),
    @("2.4", "11", "8", "1000", "calm typical twist flux"),
    @("2.5", "15", "8", "1000", "calm typical twist flux hot"),
    @("2.6", "20", "4", "800", "calm typical twist flux"),
    @("2.7", "26", "4", "600", "calm typical twist flux"),
    @("2.3", "12", "8", "1000", "calm twist flux"),
    @("2.4", "16", "8", "1000", "calm twist flux")
)
foreach ($r in $su2) {
    $b, $l, $c, $n, $bcl = $r
    $s = [int]([double]$b * 100)
    $k = 0
    foreach ($bc in $bcl.Split(" ")) {
        $k++
        RunGpu "su2_b${b}_l${l}_$bc" @("run", "su2", $b, $l, $bc, "500", $n, "$(10 * $s + 100 * [int]$l + $k)", "$out/su2_b${b}_l${l}_$bc.npz", "--chains", $c, "--smear", "8")
        PumpCoupled
    }
}
while ($cplJobs.Count -gt 0 -or @($cplRunning | Where-Object { -not $_.P.HasExited }).Count -gt 0) { PumpCoupled; Start-Sleep 30 }
PumpCoupled

# ---- 5. analysis ---------------------------------------------------------------------------------------------------------------------
& $py -W ignore analyse_boundary.py "$out/*.npz" --out "$out/boundary_summary.json" *> "$out/analysis.log"
"BOUNDARY DONE $(Get-Date -Format s)" | Add-Content $qlog
