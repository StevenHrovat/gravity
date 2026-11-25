# Leg B, SU(2) GPU phase, reordered on 2026-11-21 (about 19:45) by the owner's decision, before any of the reordered runs had data:
# the larger boxes (Q2) first, then the rest of beta 2.5, then 2.6, then 2.7 last (overnight, low load). Identical commands and seeds as
# queue_boundary_gpu.ps1 (seed = 10*int(100*beta) + 100*ell + k, k = the BC's position in the original list). The SU(2) coupled-chain
# runs on the CPU (exploratory) are paused. Waits for the run in progress (beta 2.5 twist) to finish first; the final analysis waits for
# the photon gate as before.   pwsh -File queue_boundary_gpu2.ps1
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$py = (Get-Command py).Source
$out = "runs-gpu/boundary"
$qlog = "$out/queue_boundary.log"
"REORDER: gpu part restarted $(Get-Date -Format s)" | Add-Content $qlog
while (Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match 'boundary\.py run su2 ' }) { Start-Sleep 30 }
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
# beta, ell, chains, measurements, bc, k (position in the original BC list)
$jobs = @(
    @("2.3", "12", "8", "1000", "calm", 1), @("2.3", "12", "8", "1000", "twist", 2), @("2.3", "12", "8", "1000", "flux", 3),
    @("2.4", "16", "8", "1000", "calm", 1), @("2.4", "16", "8", "1000", "twist", 2), @("2.4", "16", "8", "1000", "flux", 3),
    @("2.5", "15", "8", "1000", "flux", 4), @("2.5", "15", "8", "1000", "hot", 5),
    @("2.6", "20", "4", "800", "calm", 1), @("2.6", "20", "4", "800", "typical", 2), @("2.6", "20", "4", "800", "twist", 3), @("2.6", "20", "4", "800", "flux", 4),
    @("2.7", "26", "4", "600", "calm", 1), @("2.7", "26", "4", "600", "typical", 2), @("2.7", "26", "4", "600", "twist", 3), @("2.7", "26", "4", "600", "flux", 4)
)
foreach ($j in $jobs) {
    $b, $l, $c, $n, $bc, $k = $j
    $name = "su2_b${b}_l${l}_$bc"
    if ((Test-Path "$out/$name.npz") -and (Select-String -Path $qlog -Pattern "^$name \(gpu, attempt \d\) exit 0" -Quiet)) { continue }
    $s = [int]([double]$b * 100)
    RunGpu $name @("run", "su2", $b, $l, $bc, "500", $n, "$(10 * $s + 100 * [int]$l + $k)", "$out/$name.npz", "--chains", $c, "--smear", "8")
}
while (-not (Select-String -Path $qlog -Pattern "PHOTON TEST (PASSED|FAILED)" -Quiet)) { Start-Sleep 60 }
& $py -W ignore analyse_boundary.py "$out/*.npz" --out "$out/boundary_summary.json" *> "$out/analysis.log"
"BOUNDARY DONE $(Get-Date -Format s)" | Add-Content $qlog
