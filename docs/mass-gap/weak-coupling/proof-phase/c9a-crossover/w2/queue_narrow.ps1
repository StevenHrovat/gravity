<#
The narrow W2 run (amendment A6): 6 fused launches, 3 per beta. DRY RUN by default: prints the launches and the projection.

  pwsh -File queue_narrow.ps1                     # dry run (default): starts nothing
  pwsh -File queue_narrow.ps1 -Run -OwnerOk       # only after the owner's explicit OK on PROJECTION.md section 6

Before every launch: the GPU must be idle (below 15 % over three readings), else wait up to 10 min, then stop.
Abort rule: a launch that takes more than twice its projected time stops the queue after it. Order: beta 2.3 first.
#>
param([switch]$Run, [switch]$OwnerOk)
$ErrorActionPreference = "Stop"
Set-Location $PSScriptRoot
$proj = Get-Content "PROJECTION_narrow.json" -Raw | ConvertFrom-Json
$launches = @()
foreach ($b in @(@{beta = "2.3"; T = 300}, @{beta = "3.5"; T = 600})) {
    $launches += [pscustomobject]@{ beta = $b.beta; T = $b.T; seed = 101; jobs = "A1:8,A2:8,A3:8,A4:8,A1:0,A2:0" }
    $launches += [pscustomobject]@{ beta = $b.beta; T = $b.T; seed = 102; jobs = "A3:0,A4:0,A6:0,sampled:0,sampled:0,sampled:0" }
    $launches += [pscustomobject]@{ beta = $b.beta; T = $b.T; seed = 103; jobs = "sampled:0,sampled:0,sampled:0,sampled:0,sampled:0" }
}
$launches | Format-Table -AutoSize | Out-String -Width 200
"Projected: {0:F2} GPU-hours (PROJECTION_narrow.json)" -f $proj.total_hours
if (-not $Run) { "DRY RUN: nothing started."; exit 0 }
if (-not $OwnerOk) { throw "The narrow run needs the owner's explicit OK on the projection: pass -OwnerOk only after it." }
New-Item -ItemType Directory -Force runs\narrow | Out-Null
foreach ($L in $launches) {
    $waited = 0
    while ($true) {
        $v = @(); foreach ($i in 1..3) { $v += [int](& nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits | Select-Object -First 1); Start-Sleep 1 }
        if (($v | Measure-Object -Maximum).Maximum -lt 15) { break }
        Start-Sleep -Seconds 30; $waited += 30
        if ($waited -ge 600) { throw "GPU busy for 10 minutes; queue stopped" }
    }
    $row = $proj.rows | Where-Object { [string]$_.beta -eq $L.beta }
    $expect = ($row.main_s / 3) + $row.pool_s
    $out = "runs\narrow\launch_b$($L.beta)_s$($L.seed).json"
    $t0 = Get-Date
    & py constrained.py launch "runs\conf_b$($L.beta).npz" $L.beta $L.T $L.jobs $out --seed $L.seed --gpu --fused --force --max_seconds ([int](2 * $expect))
    $dt = ((Get-Date) - $t0).TotalSeconds
    "{0} beta={1} seed={2}: {3:F0} s (projected {4:F0} s)" -f (Get-Date -Format HH:mm:ss), $L.beta, $L.seed, $dt, $expect
    if ($dt -gt 2 * $expect) { throw "abort rule: launch took $dt s, more than twice the projected $expect s" }
}
