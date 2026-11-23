<#
The one timed W2 job, with a watcher (coordinator's conditions, 2026-11-23):
  * refuses to start unless the GPU is idle (below 15 % over three readings);
  * logs elapsed time against the estimate at checkpoints (every 30 s; kill check at most 30 s late, so the job ends by 45 min);
  * kills the job at the hard cap (45 min) whatever state it is in;
  * the job itself stops its main loop at -SoftCap seconds and writes its timing JSON, so normally it ends before the kill.
  pwsh -File time_job.ps1 -Beta 3.5 -T 400 -EstimateMin 40
#>
param([double]$Beta = 3.5, [int]$T = 400, [double]$EstimateMin = 40, [int]$HardCapSec = 2640, [int]$SoftCapSec = 2400,
      [string]$YClass = "A3", [int]$Batch = 3, [int]$Pool = 8, [int]$Ell = 6, [double]$Kappa = 16, [string]$Jobs = "")
$ErrorActionPreference = "Stop"
Set-Location $PSScriptRoot
$v = @(); foreach ($i in 1..3) { $v += [int](& nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits | Select-Object -First 1); Start-Sleep 1 }
if (($v | Measure-Object -Maximum).Maximum -ge 15) { throw "GPU not idle ($($v -join ', ') %); not starting" }
$tag = if ($Jobs) { "fused_" } else { "" }
$out = "runs\timing_${tag}b$Beta.json"
$log = "runs\timing_${tag}b$Beta.log"
$jobArgs = @("constrained.py", "job", "runs\conf_b$Beta.npz", "$Beta", "$Ell", "$Kappa", $YClass, "$T", $out,
          "--pool", "$Pool", "--batch", "$Batch", "--gpu", "--force", "--max_seconds", "$SoftCapSec")
if ($Jobs) {
    $jobArgs = @("constrained.py", "launch", "runs\conf_b$Beta.npz", "$Beta", "$T", $Jobs, $out, "--ell", "$Ell",
                 "--kappa", "$Kappa", "--gpu", "--fused", "--force", "--max_seconds", "$SoftCapSec")
}
$t0 = Get-Date
"start {0:HH:mm:ss}  beta={1} ell={2} kappa={3} {4} T={5} batch={6} pool={7} jobs={11}  estimate {8} min, soft cap {9} s, hard cap {10} s" -f $t0, $Beta, $Ell, $Kappa, $YClass, $T, $Batch, $Pool, $EstimateMin, $SoftCapSec, $HardCapSec, $Jobs | Tee-Object -FilePath $log
$p = Start-Process -FilePath "py" -ArgumentList $jobArgs -NoNewWindow -PassThru -RedirectStandardOutput "runs\timing_${tag}b$Beta.stdout" -RedirectStandardError "runs\timing_${tag}b$Beta.stderr"
while (-not $p.HasExited) {
    Start-Sleep -Seconds 30
    $el = ((Get-Date) - $t0).TotalSeconds
    $util = (& nvidia-smi --query-gpu=utilization.gpu,memory.used --format=csv,noheader) -join " "
    "checkpoint {0:F0} s ({1:F0}% of estimate)  GPU {2}" -f $el, (100 * $el / ($EstimateMin * 60)), $util | Tee-Object -FilePath $log -Append
    if ($el -ge $HardCapSec -and -not $p.HasExited) {
        "HARD CAP reached: killing the job" | Tee-Object -FilePath $log -Append
        Stop-Process -Id $p.Id -Force
        Get-CimInstance Win32_Process -Filter "ParentProcessId=$($p.Id)" | ForEach-Object { Stop-Process -Id $_.ProcessId -Force }
        break
    }
}
$el = ((Get-Date) - $t0).TotalSeconds
"end {0:HH:mm:ss}  elapsed {1:F0} s  exit {2}" -f (Get-Date), $el, $p.ExitCode | Tee-Object -FilePath $log -Append
if (Test-Path $out) { Get-Content $out | Tee-Object -FilePath $log -Append }
