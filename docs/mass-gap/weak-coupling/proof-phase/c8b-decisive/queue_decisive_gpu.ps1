# Decisive one-box measurement (PREREG.md of this folder). Do NOT start before the coordinator releases the GPU.
#   pwsh -File queue_decisive_gpu.ps1 [-DryRun] [-Tier 1|2] [-CpuParallel 4]
# -DryRun : print every job (name, device, command) and the runtime estimate, run nothing.
# Resumable: a job whose "<name> (...) exit 0" line is already in runs/queue_decisive.log is skipped; a failed job is retried (3 attempts
# for GPU jobs, only after an out-of-memory). Partial npz files from an interrupted job are overwritten by the rerun.
# Jobs: C = coupled chains (upper bound, decisive.py couple), T = tie test (decisive.py tie).
# Tier 1 = the plan of PREREG.md section 3 (all gates, the strong-coupling anchors, the saturation scan, SU(2) beta 2.3 and 2.5, the
#          tie controls Z2 / 2I and the SU(2) tie ladders up to l sqrt(sigma) about 3.1 to 4.6).
# Tier 2 = Tier 1 plus the largest tie boxes (SU(2) beta 2.3 l = 17, 21; beta 2.5 l = 21; Z2 l = 17).
# Log lines: "<name> (gpu|cpu, attempt i) exit <code> minutes <m>"; the last line of a complete run is "DECISIVE DONE <time>".
param([switch]$DryRun, [int]$Tier = 1, [int]$CpuParallel = 4)
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py -ErrorAction SilentlyContinue).Source
if (-not $py) { $py = (Get-Command python).Source }
$out = "runs"
$qlog = "$out/queue_decisive.log"
if (-not $DryRun) { New-Item -ItemType Directory -Force $out | Out-Null }
$done = @{}
if (Test-Path $qlog) {
    foreach ($l in Get-Content $qlog) { if ($l -match '^(\S+) \((gpu|cpu), attempt \d+\) exit 0 ') { $done[$Matches[1]] = $true } }
}

$gpuJobs = @()
$cpuJobs = @()
$est = @{ gpu = 0.0; cpu = 0.0 }   # seconds
# cost model, seconds per lattice site, pair (or chain) and sweep. CPU numbers are measured in the pilots of PREREG.md section 6 (couple 8e-6,
# tie z2 1.0e-5, tie i2 5e-5; single core, the machine was loaded, so these are on the high side). GPU numbers are ASSUMED (not measured: the GPU was busy): couple array code
# 4e-7 plus 0.1 s of launch overhead per sweep; tie su2 on the fused kernels 1.0e-6 (c7b: 1.5e-6 per site, chain and 2 sweeps).
function Site-Count([int]$ell) { $N = if ($ell % 2 -eq 0) { $ell + 2 } else { $ell + 3 }; return [math]::Pow($N, 4) }
function Ncell-For([int]$ell, [double]$beta) {
    # cell side about 0.70 / sqrt(sigma) at beta 2.3 / 2.5 (ell / 2 and ell / 3.7 cells); strong coupling: ell / 2
    if ($beta -ge 2.4) { return [int][math]::Max(2, [math]::Round($ell / 3.7)) }
    return [int][math]::Max(2, [math]::Round($ell / 2.0))
}
function Nclass([int]$nc, [int]$cap = 0) {
    $d = @(0..($nc - 1) | ForEach-Object { [math]::Min($_, $nc - 1 - $_) })
    if ($cap -gt 0) { $d = @($d | ForEach-Object { [math]::Min($_, $cap) }) }
    $set = @{}
    foreach ($i in $d) { foreach ($j in $d) { foreach ($k in $d) { $key = (@($i, $j, $k) | Sort-Object) -join ","; $set[$key] = 1 } } }
    return $set.Count
}

function Add-Couple([string]$name, [string]$group, [double]$beta, [int]$ell, [string]$bg, [string]$dev, [string[]]$extra, [int]$chains, [int]$therm, [int]$meas, [int]$nc = 0) {
    if ($nc -eq 0) { $nc = Ncell-For $ell $beta }
    $a = @("decisive.py", "couple", $group, "$beta", "$ell", $bg, "$out/$name.npz", "--ncell", "$nc", "--chains", "$chains", "--therm", "$therm",
           "--meas", "$meas", "--every", "2", "--seed", "$(500 + $ell)") + $extra
    $cap = 0
    for ($i = 0; $i -lt $extra.Count - 1; $i++) { if ($extra[$i] -eq "--depth-cap") { $cap = [int]$extra[$i + 1] } }
    $pairs = $chains * (Nclass $nc $cap)
    $sweeps = $therm + 2 * $meas
    $job = @{ N = $name; A = $a; D = $dev; E = 0.0 }
    if ($dev -eq "gpu") { $job.E = 4.0e-7 * (Site-Count $ell) * $pairs * $sweeps + 0.1 * $sweeps; $script:gpuJobs += , $job; $script:est.gpu += $job.E }
    else { $job.E = 8.0e-6 * (Site-Count $ell) * $pairs * $sweeps; $job.A = $a + @("--cpu"); $script:cpuJobs += , $job; $script:est.cpu += $job.E }
}

function Add-Tie([string]$group, [double]$beta, [int]$ell, [string]$dev, [int]$chains, [int]$meas, [int]$stepTherm = 40, [int]$nodes = 5, [int]$therm = 200) {
    foreach ($sec in @("A", "B")) {
        $name = "{0}_b{1}_l{2}_tie{3}" -f $group, $beta, $ell, $sec
        $a = @("decisive.py", "tie", $group, "$beta", "$ell", $sec, "$out/$name.npz", "--chains", "$chains", "--therm", "$therm", "--nodes", "$nodes",
               "--step-therm", "$stepTherm", "--meas", "$meas", "--every", "2", "--seed", "$(700 + $ell)")
        $sweeps = $therm + $nodes * ($stepTherm + 2 * $meas)
        $job = @{ N = $name; A = $a; D = $dev; E = 0.0 }
        if ($dev -eq "gpu") { $job.E = 1.0e-6 * (Site-Count $ell) * $chains * $sweeps + $nodes * 3; $script:gpuJobs += , $job; $script:est.gpu += $job.E }
        else {
            $c = if ($group -eq "i2") { 5.0e-5 } else { 1.0e-5 }
            $job.E = $c * (Site-Count $ell) * $chains * $sweeps
            $job.A = $a + @("--cpu"); $script:cpuJobs += , $job; $script:est.cpu += $job.E
        }
    }
}

# ---- U: the coupled-chain upper bound -----------------------------------------------------------------------------------------------
# gates (CPU, small): identical boundaries, gauge-rotated start (aligned and not), pure-gauge boundary change (labels allowed and not)
Add-Couple "gate_ident_su2_l6"      "su2" 2.3 6 "calm" "cpu" @("--pert", "none", "--init", "same") 2 20 40
Add-Couple "gate_rot_ham_su2_l6"    "su2" 2.3 6 "calm" "cpu" @("--pert", "none", "--init", "rot") 2 20 40
Add-Couple "gate_rot_none_su2_l6"   "su2" 2.3 6 "calm" "cpu" @("--pert", "none", "--init", "rot", "--align", "none") 2 20 40
Add-Couple "gate_gauge_lab1_su2_l6" "su2" 2.3 6 "calm" "cpu" @("--pert", "gauge", "--boundary-labels", "1") 2 20 40
Add-Couple "gate_gauge_lab0_su2_l6" "su2" 2.3 6 "calm" "cpu" @("--pert", "gauge", "--boundary-labels", "0") 2 20 40
Add-Couple "gate_indep_su2_b0.1_l6" "su2" 0.1 6 "calm" "cpu" @("--pert", "none", "--init", "indep") 2 60 40
# strong-coupling anchors, the informative regime of the coupling (cell side 2). Depth classes merged above 2 for nc > 6 (influence is local)
foreach ($l in 8, 12, 16, 24) {
    $cap = if ($l -ge 16) { @("--depth-cap", "2") } else { @() }
    $chn = if ($l -ge 16) { 2 } else { 4 }
    Add-Couple "anchor_su2_b0.1_l${l}_calm" "su2" 0.1 $l "calm" "gpu" (@("--pert", "flip") + $cap) $chn 60 150
    if ($l -le 16) { Add-Couple "anchor_su2_b0.1_l${l}_rand" "su2" 0.1 $l "calm" "gpu" (@("--pert", "rand") + $cap) 4 60 150 }
}
foreach ($l in 8, 12) { Add-Couple "anchor_su2_b0.2_l${l}_calm" "su2" 0.2 $l "calm" "gpu" @("--pert", "flip") 4 60 150 }
Add-Couple "anchor_su2_b0.1_l8_typical" "su2" 0.1 8 "typical" "gpu" @("--pert", "flip", "--periodic-therm", "60") 4 60 150
# saturation scan at one box size: where does the coupling stop being informative
foreach ($b in 0.3, 0.5, 0.8, 1.2, 1.8) { Add-Couple "scan_su2_b${b}_l8_calm" "su2" $b 8 "calm" "gpu" @("--pert", "flip") 2 40 40 }
# weak coupling: the Tier-1 boxes of c7b (expected saturated, PREREG.md section 2). calm everywhere, typical and hot at one box each
foreach ($w in @(@(2.3, 6), @(2.3, 8), @(2.3, 10), @(2.3, 12), @(2.5, 11), @(2.5, 15))) {
    $b = $w[0]; $l = $w[1]
    Add-Couple "weak_su2_b${b}_l${l}_calm" "su2" $b $l "calm" "gpu" @("--pert", "flip") 2 40 40
}
foreach ($bg in "typical", "hot") {
    Add-Couple "weak_su2_b2.3_l6_${bg}" "su2" 2.3 6 $bg "gpu" @("--pert", "flip", "--periodic-therm", "100") 2 40 40
    Add-Couple "weak_su2_b2.5_l11_${bg}" "su2" 2.5 11 $bg "gpu" @("--pert", "flip", "--periodic-therm", "100") 2 40 40
}
# U(1): photon (must be saturated) and a strong-coupling U(1) (local), CPU
Add-Couple "photon_u1_b2_l6"      "u1" 2.0 6 "calm" "cpu" @("--pert", "flip") 2 30 40
Add-Couple "photon_u1_b2_l8"      "u1" 2.0 8 "calm" "cpu" @("--pert", "flip") 2 30 40
Add-Couple "u1strong_u1_b0.05_l6" "u1" 0.05 6 "calm" "cpu" @("--pert", "flip") 4 30 60
Add-Couple "u1strong_u1_b0.05_l8" "u1" 0.05 8 "calm" "cpu" @("--pert", "flip") 4 30 60

# ---- T: the tie test -----------------------------------------------------------------------------------------------------------------
# box sizes l = 4 s + 1 make the two sheet arrangements equal in area (flat sheets 2 (l - 1)^2 plaquettes, tube 8 s (l - 1)).
# controls (CPU): Z2 deconfined (must be a TIE), Z2 confined (must be NO TIE), 2I beta 6 (sheets 5 lattice units thick, loop R = 5; beta 4 is not
# resolved by the loops, beta 8 is frozen: PREREG.md section 2.5)
foreach ($l in 9, 13) { Add-Tie "z2" 0.6 $l "cpu" 6 60 20 }
foreach ($l in 9, 13) { Add-Tie "z2" 0.3 $l "cpu" 6 60 20 }
Add-Tie "i2" 6.0 13 "cpu" 3 30 20 5 100
# SU(2), GPU: beta 2.3 (l sqrt(sigma) = 1.75, 3.2, 4.6) and beta 2.5 (1.6, 2.4, 3.1)
foreach ($l in 5, 9, 13) { Add-Tie "su2" 2.3 $l "gpu" 8 100 40 }
foreach ($l in 9, 13, 17) { Add-Tie "su2" 2.5 $l "gpu" 8 100 40 }
if ($Tier -ge 2) { Add-Couple "anchor_su2_b0.1_l36_calm" "su2" 0.1 36 "calm" "gpu" @("--pert", "flip", "--depth-cap", "2") 2 60 150 }
if ($Tier -ge 2) { Add-Tie "su2" 2.3 17 "gpu" 8 100 40; Add-Tie "su2" 2.5 21 "gpu" 8 100 40; Add-Tie "z2" 0.6 17 "cpu" 6 60 20; Add-Tie "i2" 6.0 17 "cpu" 3 30 20 5 100; Add-Tie "su2" 2.3 21 "gpu" 8 100 40 }

if ($DryRun) {
    foreach ($j in $gpuJobs + $cpuJobs) { "{0,-34} {1} est {2,6:N1} min  {3} {4}" -f $j.N, $j.D, ($j.E / 60), $py, ($j.A -join " ") }
    "jobs: $($gpuJobs.Count) gpu, $($cpuJobs.Count) cpu; already done: $($done.Count)"
    "estimated GPU time: {0:N1} h (+/- factor 3), GPU jobs run one after another" -f ($est.gpu / 3600)
    "estimated CPU time: {0:N1} CPU-hours, run $CpuParallel at a time beside the GPU jobs: about {1:N1} h wall" -f ($est.cpu / 3600), ($est.cpu / 3600 / $CpuParallel)
    "dry run: nothing started"
    return
}

# ---- run -----------------------------------------------------------------------------------------------------------------------------
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
& $py -B decisive.py analyse $out --out "$out/decisive_summary.json" *> "$out/analysis.log"
"analysis exit $LASTEXITCODE" | Add-Content $qlog
"DECISIVE DONE $(Get-Date -Format s)" | Add-Content $qlog
