# c5e-dmp: the joint measurement of z0(L) and z_e(L), pre-registered in PREREG-JOINT.md (this folder). Started by the coordinating session only.
#   pwsh -File queue_joint_gpu.ps1                       the real queue (GPU)
#   pwsh -File queue_joint_gpu.ps1 -DryRun               prints every command, runs nothing, creates no file
#   pwsh -File queue_joint_gpu.ps1 -DryRun -SimulateUsPerSiteSweep 1.0   dry run that also tests the projection and the cut rule
# Steps: run 0 = lattice/run_su2_gpu.py selftest (stop on failure); runs 1-13 of the prereg's Runs table (T = 32, therm 500, every 2, 10 chains,
# 3 overrelaxation steps, levels 2,6,12,20; seed 900 + 100 * (beta index) + L (coordinator amendment: avoids the 926 collision) with beta index 0, 1, 2 for beta 2.3, 2.4, 2.5);
# after runs 1 and 2 a projection of the whole plan from their measured speed; if it exceeds 4 h, runs 9, 13, 4 are dropped in this order
# until it fits (the prereg's cut rule). The optional run 14 is not part of this queue.
# Then the analysis (analyse_joint.py, CPU), and the last line of the queue log is "JOINT DONE ...".
# Output: runs-gpu/joint_b<beta>_L<L>.npz and .log, runs-gpu/queue_joint.log, runs-gpu/joint_summary.json, joint_report.txt, joint_z.png.
# Resumable: a run whose .npz exists and whose "exit 0" line is in the queue log is skipped on a restart.
param([switch]$DryRun, [double]$SimulateUsPerSiteSweep = 0, [double]$LimitHours = 4.0)
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$inv = [Globalization.CultureInfo]::InvariantCulture
$runner = (Resolve-Path (Join-Path $PSScriptRoot "../../../lattice/run_su2_gpu.py")).Path
$out = Join-Path $PSScriptRoot "runs-gpu"
$qlog = Join-Path $out "queue_joint.log"
$T = 32; $therm = 500; $every = 2; $chains = 10; $nor = 3; $levels = "2,6,12,20"

# run id, beta (text, locale independent), beta index, L, measurements
$plan = @(
    @(1, "2.3", 0, 4, 2000), @(2, "2.3", 0, 6, 2000), @(3, "2.3", 0, 8, 2000), @(4, "2.3", 0, 12, 1500),
    @(5, "2.4", 1, 4, 2000), @(6, "2.4", 1, 6, 2000), @(7, "2.4", 1, 8, 2000), @(8, "2.4", 1, 12, 1500), @(9, "2.4", 1, 16, 1000),
    @(10, "2.5", 2, 6, 2000), @(11, "2.5", 2, 8, 2000), @(12, "2.5", 2, 12, 1500), @(13, "2.5", 2, 16, 1000)
) | ForEach-Object {
    [pscustomobject]@{ Id = $_[0]; Beta = $_[1]; L = $_[3]; Meas = $_[4]; Seed = 900 + 100 * $_[2] + $_[3];
        Name = "joint_b$($_[1])_L$($_[3])"; Work = [double]$_[3] * $_[3] * $_[3] * $T * ($therm + $every * $_[4]) * $chains }
}

function Log([string]$msg) {
    $line = "$msg"
    Write-Host $line
    if (-not $DryRun) { Add-Content -Path $qlog -Value $line }
}
if (-not $DryRun) {
    New-Item -ItemType Directory -Force $out | Out-Null
    $py = (Get-Command py).Source
} else { $py = "py" }
Log "JOINT QUEUE START $(Get-Date -Format s)$(if ($DryRun) { ' (dry run)' })"

# run 0: GPU self-test
if ($DryRun) {
    Log "[dry] $py $runner selftest > runs-gpu/selftest.log   (must print OK, else the queue stops)"
} else {
    & $py $runner selftest *> (Join-Path $out "selftest.log")
    $code = $LASTEXITCODE
    $ok = (Select-String -Path (Join-Path $out "selftest.log") -Pattern "^OK" -Quiet)
    if ($code -ne 0 -or -not $ok) { Log "run 0 selftest FAILED (exit $code): queue stopped $(Get-Date -Format s)"; exit 1 }
    Log "run 0 selftest exit 0 OK"
}

function RunOne($r) {
    $npz = Join-Path $out "$($r.Name).npz"
    $log = Join-Path $out "$($r.Name).log"
    $cmd = @($runner, $r.Beta, $r.L, $T, $therm, $r.Meas, $r.Seed, $npz, $nor, $every, $chains, $levels)
    if ($DryRun) { Log "[dry] run $($r.Id): $py -u $($cmd -join ' ') > $log"; return }
    if ((Test-Path $npz) -and (Select-String -Path $qlog -Pattern "^run $($r.Id) .* exit 0" -Quiet)) {
        Log "run $($r.Id) $($r.Name) already done, skipped"; return
    }
    for ($i = 1; $i -le 2; $i++) {
        $t = Get-Date
        & $py -u @cmd *> $log
        $code = $LASTEXITCODE
        Log "run $($r.Id) $($r.Name) (attempt $i) exit $code minutes $([int]((Get-Date) - $t).TotalMinutes)"
        if ($code -eq 0) { return }
        Start-Sleep 60
    }
    $script:failed += $r.Id
}

function SecondsOf($r) {
    if ($SimulateUsPerSiteSweep -gt 0) { return $r.Work * $SimulateUsPerSiteSweep * 1e-6 + 25 }
    $log = Join-Path $out "$($r.Name).log"
    if (-not (Test-Path $log)) { return $null }
    $m = Select-String -Path $log -Pattern "^done .* in (\d+)s" | Select-Object -Last 1
    if (-not $m) { return $null }
    return [double]$m.Matches[0].Groups[1].Value
}

$script:failed = @()
$dropped = @()
foreach ($r in $plan) {
    if ($dropped -contains $r.Id) { Log "run $($r.Id) $($r.Name) DROPPED by the cut rule"; continue }
    RunOne $r
    if ($r.Id -eq 2) {
        # projection from runs 1 and 2 (their measured time per site and sweep, start-up included: slightly pessimistic)
        $s1 = SecondsOf $plan[0]; $s2 = SecondsOf $plan[1]
        if ($null -eq $s1 -or $null -eq $s2) {
            Log "PROJECTION not possible (run 1 or 2 has no 'done ... in Ns' line): plan unchanged"
        } else {
            $rate = ($s1 + $s2) / ($plan[0].Work + $plan[1].Work)
            $cuts = @(9, 13, 4)
            while ($true) {
                $rest = ($plan | Where-Object { $_.Id -gt 2 -and $dropped -notcontains $_.Id } | Measure-Object -Property Work -Sum).Sum
                $totalH = ($s1 + $s2 + $rest * $rate) / 3600
                Log ("PROJECTED TOTAL {0:N2} h (rate {1:N3} us per site and sweep from runs 1-2; limit {2:N1} h; dropped: {3})" -f $totalH, ($rate * 1e6), $LimitHours, ($(if ($dropped.Count) { $dropped -join ',' } else { 'none' })))
                if ($totalH -le $LimitHours -or $dropped.Count -ge $cuts.Count) { break }
                $dropped += $cuts[$dropped.Count]
                Log "CUT RULE: projection above $LimitHours h, run $($cuts[$dropped.Count - 1]) dropped"
            }
        }
    }
}

# analysis (CPU only)
$files = Join-Path $out "joint_b*.npz"
$an = @("-W", "ignore", (Join-Path $PSScriptRoot "analyse_joint.py"), $files, "--label", "joint measurement (T = 32)",
        "--out", (Join-Path $out "joint_summary.json"), "--report", (Join-Path $out "joint_report.txt"), "--plot", (Join-Path $out "joint_z.png"))
if ($DryRun) {
    Log "[dry] CUDA_VISIBLE_DEVICES=-1 $py $($an -join ' ') > runs-gpu/analysis.log"
    Log "JOINT DONE (dry run)"
} else {
    $env:CUDA_VISIBLE_DEVICES = "-1"
    & $py @an *> (Join-Path $out "analysis.log")
    Log "analysis exit $LASTEXITCODE"
    Log "JOINT DONE $(Get-Date -Format s) failed runs: $(if ($script:failed.Count) { $script:failed -join ',' } else { 'none' }); dropped by the cut rule: $(if ($dropped.Count) { $dropped -join ',' } else { 'none' })"
}
