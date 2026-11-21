# Leg B, SU(2) phase (GPU) and SU(2) coupled chains (CPU), split from queue_boundary.ps1 on 2026-11-21 and started before the photon
# gate (the owner's decision, to save about 3 hours): identical commands and seeds. The gate (queue_boundary_cpu.ps1) still decides whether
# these SU(2) results count as evidence; if it fails they are not used. The final analysis waits for the gate.
#   pwsh -File queue_boundary_gpu.ps1
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py).Source
$out = "runs-gpu/boundary"
New-Item -ItemType Directory -Force $out | Out-Null
$qlog = "$out/queue_boundary.log"


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
"SPLIT: gpu part started before the gate $(Get-Date -Format s)" | Add-Content $qlog

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

while (-not (Select-String -Path $qlog -Pattern "PHOTON TEST (PASSED|FAILED)" -Quiet)) { Start-Sleep 60 }
# ---- 5. analysis ---------------------------------------------------------------------------------------------------------------------
& $py -W ignore analyse_boundary.py "$out/*.npz" --out "$out/boundary_summary.json" *> "$out/analysis.log"
"BOUNDARY DONE $(Get-Date -Format s)" | Add-Content $qlog
