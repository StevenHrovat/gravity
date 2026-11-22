# One-box worst-case-boundary measurement (PREREG.md). Do NOT start before the coordinator releases the GPU.
#   pwsh -File queue_onebox_gpu.ps1 [-DryRun] [-Tier 1|2] [-CpuParallel 4]
# -DryRun : print every job (name, device, command) and the runtime estimate, run nothing.
# Resumable: a job whose "<name> ... exit 0" line is already in runs/queue_onebox.log is skipped; a failed job is retried (3 attempts,
# the GPU ones only after an out-of-memory). Partial npz files from an interrupted job are overwritten by the rerun.
# Amended by PREREG-AMEND.md: tie backgrounds added, twist only as extreme pair.
# Tier 1 = the core plan (SU(2) beta 2.3 ell 6..10,12; beta 2.5 ell 11,15; strong coupling anchor; all controls).
# Tier 2 = Tier 1 plus beta 2.5 ell 19.
# Log lines: "<name> (gpu|cpu, attempt i) exit <code> minutes <m>"; the last line of a complete run is "ONEBOX DONE <time>".
param([switch]$DryRun, [int]$Tier = 2, [int]$CpuParallel = 4)
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py -ErrorAction SilentlyContinue).Source
if (-not $py) { $py = (Get-Command python).Source }
$out = "runs"
$qlog = "$out/queue_onebox.log"
if (-not $DryRun) { New-Item -ItemType Directory -Force $out | Out-Null }
$done = @{}
if (Test-Path $qlog) {
    foreach ($l in Get-Content $qlog) { if ($l -match '^(\S+) \((gpu|cpu), attempt \d+\) exit 0 ') { $done[$Matches[1]] = $true } }
}

# ---- job tables -------------------------------------------------------------------------------------------------------------------
$gpuJobs = @()
$cpuJobs = @()
$est = @{ gpu = 0.0; cpu = 0.0 }   # seconds; GPU: 1.5e-6 s per site, chain and measurement (PREREG.md); CPU: filled from the pilot

function Add-Set([string]$group, [double]$beta, [int]$ell, [int]$chains, [int]$meas, [string]$dev, [string[]]$bgs, [switch]$extraPatch) {
    # one (group, beta, ell): for every background the unchanged box (patch 0), a small patch, a half-face patch, the whole face;
    # on 'calm' also the gauge control (whole boundary re-gauged). Same seed within the set => same boundary for every variant.
    $h = [int][math]::Ceiling($ell / 2)
    $N = if ($ell % 2 -eq 0) { $ell + 2 } else { $ell + 3 }
    foreach ($bg in $bgs) {
        $variants = @(@(0, "flip"), @($ell, "flip"))
        if ($bg -eq "twist") { $variants = @(@(0, "flip")) }   # amendment: twist only as an extreme pair against calm
        if ($bg -in @("calm", "typical")) { $variants = @(@(0, "flip"), @(2, "flip"), @($h, "flip"), @($ell, "flip")) }
        if ($bg -eq "calm") { $variants += , @($ell, "gauge") }
        foreach ($v in $variants) {
            $p = $v[0]; $pert = $v[1]
            $name = "{0}_b{1}_l{2}_{3}_p{4}{5}" -f $group, $beta, $ell, $bg, $p, $(if ($pert -eq "gauge") { "g" } else { "" })
            $a = @("onebox.py", "run", $group, "$beta", "$ell", $bg, "$out/$name.npz", "--patch", "$p", "--pert", $pert,
                   "--chains", "$chains", "--therm", "200", "--meas", "$meas", "--seed", "$(1000 + $ell)")
            $job = @{ N = $name; A = $a; D = $dev }
            if ($dev -eq "gpu") { $script:gpuJobs += , $job; $script:est.gpu += 1.5e-6 * [math]::Pow($N, 4) * $chains * ($meas + 100) }
            else { $a += "--cpu"; $job.A = $a; $script:cpuJobs += , $job }
        }
    }
}

function Add-Tie([string]$group, [double]$beta, [int]$ell, [int]$chains, [int]$meas, [string]$dev) {
    # PREREG-AMEND.md: the tie background (two thin vortex sheets at +/- ell/4: flat sheets or a tube, equal area) and the same with
    # ONE shell cell changed (the tie breaker); both runs share the seed.
    $N = if ($ell % 2 -eq 0) { $ell + 2 } else { $ell + 3 }
    foreach ($pert in @("flip", "tiebreak")) {
        $name = "{0}_b{1}_l{2}_tie_{3}" -f $group, $beta, $ell, $pert
        $a = @("onebox.py", "run", $group, "$beta", "$ell", "tie", "$out/$name.npz", "--pert", $pert,
               "--chains", "$chains", "--therm", "200", "--meas", "$meas", "--seed", "$(if ($pert -eq 'tiebreak') { 2000 + $ell } else { 1000 + $ell })")
        $job = @{ N = $name; A = $a; D = $dev }   # independent seeds for the pair: shared random numbers merge deconfined pairs exactly
        if ($dev -eq "gpu") { $script:gpuJobs += , $job; $script:est.gpu += 1.5e-6 * [math]::Pow($N, 4) * $chains * ($meas + 100) }
        else { $a += "--cpu"; $job.A = $a; $script:cpuJobs += , $job }
    }
}

# SU(2), GPU (fused kernels). Chains x measurements chosen to keep the plan near 3 h (Tier 1) / 5 h (Tier 2).
foreach ($l in 6, 8, 10, 12) { Add-Set "su2" 2.3 $l 6 600 "gpu" @("calm", "typical", "twist", "hot"); Add-Tie "su2" 2.3 $l 6 600 "gpu" }   # l sqrt(sigma) 2.1 2.8 3.5 4.2
foreach ($l in 11, 15) { Add-Set "su2" 2.5 $l 4 400 "gpu" @("calm", "typical", "twist", "hot"); Add-Tie "su2" 2.5 $l 4 400 "gpu" }          # 2.0 2.7
if ($Tier -ge 2) { Add-Set "su2" 2.5 19 4 400 "gpu" @("calm", "typical", "twist", "hot"); Add-Tie "su2" 2.5 19 4 400 "gpu" }             # 3.5
# anchor: strong-coupling SU(2) (passes)
foreach ($l in 6, 8, 10) { Add-Set "su2" 0.8 $l 4 400 "gpu" @("calm", "typical", "twist") }

# controls, CPU array code (boundary.py's U(1) and Z2 updaters), 4 chains
foreach ($l in 4, 6, 8, 10) {
    Add-Set "u1" 2.0 $l 4 400 "cpu" @("calm", "flux")        # photon at beta = 2 (must FAIL)
    Add-Set "z2" 0.6 $l 4 400 "cpu" @("calm", "twist")       # Z2 deconfined (must FAIL)
    Add-Set "z2" 0.3 $l 4 400 "cpu" @("calm", "twist")       # Z2 confined (must PASS)
    if ($l -ge 6) { Add-Tie "z2" 0.6 $l 4 400 "cpu"; Add-Tie "z2" 0.3 $l 4 400 "cpu" }   # tie control: deconfined must be bistable
}

if ($DryRun) {
    foreach ($j in $gpuJobs + $cpuJobs) { "{0,-34} {1}  {2} {3}" -f $j.N, $j.D, $py, ($j.A -join " ") }
    "jobs: $($gpuJobs.Count) gpu, $($cpuJobs.Count) cpu; already done: $($done.Count)"
    "estimated GPU time: {0:N1} h (+/- 50 %), GPU jobs run one after another" -f ($est.gpu / 3600)
    "CPU controls: run $CpuParallel at a time beside the GPU jobs, estimated 2 to 3 h wall (see PREREG.md; pilot-based)"
    "dry run: nothing started"
    return
}

# ---- run --------------------------------------------------------------------------------------------------------------------------
function Run-Gpu($j) {
    for ($i = 1; $i -le 3; $i++) {
        $t = Get-Date
        & $py -W ignore -B @($j.A) *> "$out/$($j.N).log"
        $code = $LASTEXITCODE
        "$($j.N) (gpu, attempt $i) exit $code minutes $([int]((Get-Date) - $t).TotalMinutes)" | Add-Content $qlog
        if ($code -eq 0) { return }
        if (-not (Select-String -Path "$out/$($j.N).log" -Pattern "OUT_OF_MEMORY" -Quiet)) { return }
        Start-Sleep 120
    }
}
$running = @()
$seen = @()
function Pump-Cpu {
    foreach ($r in @($script:running | Where-Object { $_.P.HasExited -and ($script:seen -notcontains $_.N) })) {
        "$($r.N) (cpu, attempt 1) exit $($r.P.ExitCode) minutes $([int]((Get-Date) - $r.T).TotalMinutes)" | Add-Content $qlog
        $script:seen += $r.N
    }
    while ($script:cpuJobs.Count -gt 0 -and @($script:running | Where-Object { -not $_.P.HasExited }).Count -lt $CpuParallel) {
        $j = $script:cpuJobs[0]
        $script:cpuJobs = @($script:cpuJobs | Select-Object -Skip 1)
        if ($done.ContainsKey($j.N)) { continue }
        $env:CUDA_VISIBLE_DEVICES = "-1"
        $p = Start-Process -FilePath $py -ArgumentList (@("-W", "ignore", "-B") + $j.A) -NoNewWindow -PassThru `
            -RedirectStandardOutput "$out/$($j.N).log" -RedirectStandardError "$out/$($j.N).err"
        Remove-Item Env:CUDA_VISIBLE_DEVICES
        $script:running += [pscustomobject]@{ N = $j.N; P = $p; T = Get-Date }
    }
}
"START $(Get-Date -Format s) tier $Tier" | Add-Content $qlog
foreach ($j in $gpuJobs) {
    Pump-Cpu
    if ($done.ContainsKey($j.N)) { continue }
    Run-Gpu $j
}
while ($cpuJobs.Count -gt 0 -or @($running | Where-Object { -not $_.P.HasExited }).Count -gt 0) { Pump-Cpu; Start-Sleep 20 }
Pump-Cpu
& $py -B onebox.py analyse $out --out "$out/onebox_summary.json" *> "$out/analysis.log"
"analysis exit $LASTEXITCODE" | Add-Content $qlog
"ONEBOX DONE $(Get-Date -Format s)" | Add-Content $qlog
