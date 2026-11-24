<#
W2 queue (W2-PREREG.md section 8, amendments A1-A5 in PIPELINE.md). Default is a DRY RUN: it prints the job table (launch
batches) and the projected time from PROJECTION.json, and starts nothing.

  pwsh -File queue_w2.ps1                          # dry run (default)
  pwsh -File queue_w2.ps1 -Run -OwnerOk            # the full run; only after the owner's explicit OK on the projection
  pwsh -File queue_w2.ps1 -Run -OwnerOk -Ladder 2  # with the pre-registered cuts (i)..(ii)

Before every launch batch the GPU must be idle (utilisation below 15 % over three readings); otherwise the queue waits up to
10 minutes, then stops. Abort rule: a batch that takes more than twice its projected time stops the queue after it.
Not runnable yet: U(1) and 2I (no sampler path), A5 (no adjoint generator); they are listed and skipped.
#>
param([switch]$Run, [switch]$OwnerOk, [int]$Ladder = 0, [string]$Projection = "PROJECTION.json")
$ErrorActionPreference = "Stop"
Set-Location $PSScriptRoot

function Test-GpuIdle {
    $v = @()
    foreach ($i in 1..3) {
        $v += [int](& nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits | Select-Object -First 1)
        Start-Sleep -Seconds 1
    }
    return (($v | Measure-Object -Maximum).Maximum -lt 15)
}

$proj = Get-Content $Projection -Raw | ConvertFrom-Json
$T = @{ "2.3" = $proj.T."2.3"; "2.6" = $proj.T."2.6"; "3.0" = $proj.T."3.0"; "3.5" = $proj.T."3.5" }
$betas = @("2.3", "2.6", "3.0", "3.5")
$kappas = @(4, 16)
if ($Ladder -ge 1) { $bk = @(); foreach ($b in $betas) { $bk += ,@($b, 16) }; $bk += ,@("2.3", 4); $bk += ,@("3.5", 4) }
else { $bk = @(); foreach ($b in $betas) { foreach ($k in $kappas) { $bk += ,@($b, $k) } } }
$nSampled = if ($Ladder -ge 3) { 8 } else { 16 }

$jobs = @()
foreach ($p in $bk) {
    $b = $p[0]; $k = $p[1]
    $ells = if ($Ladder -ge 2 -and $b -ne "2.3") { @(6) } else { @(4, 6) }
    foreach ($ell in $ells) {
        $cap = if ($ell -eq 6) { 3 } else { 6 }
        $classes = @(@("sampled", 0, $nSampled))
        foreach ($c in @("A1", "A2", "A3", "A4", "A5")) { $classes += ,@($c, 0, 1); $classes += ,@($c, 8, 1) }
        $classes += ,@("A5b", 0, 1); $classes += ,@("A5b", 8, 1); $classes += ,@("A5c", 0, 1); $classes += ,@("A5c", 8, 1)
        $classes += ,@("A6", 0, 1)
        foreach ($c in $classes) {
            $n = $c[2]; $done = 0
            while ($done -lt $n) {
                $bt = [Math]::Min($cap, $n - $done)
                $jobs += [pscustomobject]@{ beta = $b; kappa = $k; ell = $ell; yclass = $c[0]; pool = $c[1]; batch = $bt; T = $T[$b] }
                $done += $bt
            }
        }
    }
}
"{0} launch batches (SU(2) only; U(1) and 2I not runnable yet)" -f $jobs.Count
$jobs | Format-Table -AutoSize | Out-String -Width 200
"Projected total (PROJECTION.json, ladder $Ladder): {0} GPU-hours" -f $proj.ladder_hours[$Ladder]

if (-not $Run) { "DRY RUN: nothing started."; exit 0 }
if (-not $OwnerOk) { throw "The full run needs the owner's explicit OK on the projection: pass -OwnerOk only after it." }
New-Item -ItemType Directory -Force runs\production | Out-Null
foreach ($j in $jobs) {
    if ($j.yclass -like "A5*") { "skip $($j.yclass): no adjoint generator"; continue }
    $waited = 0
    while (-not (Test-GpuIdle)) { Start-Sleep -Seconds 30; $waited += 30; if ($waited -ge 600) { throw "GPU busy for 10 minutes; queue stopped" } }
    $conf = "runs\conf_b$($j.beta).npz"
    $out = "runs\production\job_b$($j.beta)_k$($j.kappa)_l$($j.ell)_$($j.yclass)_p$($j.pool)_$([guid]::NewGuid().ToString().Substring(0,8)).json"
    $t0 = Get-Date
    & py constrained.py job $conf $j.beta $j.ell $j.kappa $j.yclass $j.T $out --pool $j.pool --batch $j.batch --gpu
    $dt = ((Get-Date) - $t0).TotalSeconds
    $limit = 2 * $proj.batch_seconds."$($j.ell)"."$($j.beta)"
    if ($dt -gt $limit) { throw "abort rule: batch took $dt s, more than twice the projected $($limit/2) s" }
}
