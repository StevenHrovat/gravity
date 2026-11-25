# Leg B, phase 1 (controls on the CPU) and the photon gate, split from queue_boundary.ps1 on 2026-11-21 so that the SU(2) GPU phase
# (queue_boundary_gpu.ps1) can run at the same time: identical commands and seeds; jobs already started by the first queue process are
# skipped (their .log exists) and waited for before the gate.   pwsh -File queue_boundary_cpu.ps1
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py).Source
$out = "runs-gpu/boundary"
$qlog = "$out/queue_boundary.log"
"SPLIT: cpu part restarted $(Get-Date -Format s)" | Add-Content $qlog
function RunCpuBatch([object[]]$jobs, [int]$parallel = 8) {
    # CPU jobs never see the GPU; at most $parallel at once; returns when all have finished
    $running = @()
    foreach ($j in $jobs) {
        if (Test-Path "$out/$($j.N).log") { continue }   # started by the first queue process (split 2026-11-21)
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
# wait for the control jobs started by the first queue process (not tracked here)
while (Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match 'boundary\.py (run|couple) (u1|z2) ' }) { Start-Sleep 30 }
"controls finished $(Get-Date -Format s)" | Add-Content $qlog
& $py -W ignore analyse_boundary.py "$out/u1_*.npz" "$out/u1phi05_*.npz" "$out/z2_*.npz" "$out/cpl_u1_*.npz" "$out/cpl_z2_*.npz" --out "$out/controls_summary.json" --photon-gate *> "$out/controls_analysis.log"
if ($LASTEXITCODE -ne 0) {
    "PHOTON TEST FAILED or incomplete (analyse_boundary.py exit $LASTEXITCODE): SU(2) results not used as evidence; see $out/controls_analysis.log" | Add-Content $qlog
    "BOUNDARY DONE (stopped at the photon gate)" | Add-Content $qlog
    exit 1
}
"PHOTON TEST PASSED $(Get-Date -Format s)" | Add-Content $qlog
