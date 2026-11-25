<#
Watcher for the narrow W2 production run (owner's OK, 2026-11-23): checks the GPU is idle, starts queue_narrow.ps1 -Run
-OwnerOk as one child process, logs elapsed time against the projection every 60 s, and kills the whole process tree at the
hard cap (3 h) whatever state it is in.
  pwsh -File run_narrow.ps1
#>
param([int]$HardCapSec = 10800, [double]$ProjectionH = 1.55)
$ErrorActionPreference = "Stop"
Set-Location $PSScriptRoot
New-Item -ItemType Directory -Force runs\narrow | Out-Null
$log = "runs\narrow\watcher.log"
$v = @(); foreach ($i in 1..3) { $v += [int](& nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits | Select-Object -First 1); Start-Sleep 1 }
if (($v | Measure-Object -Maximum).Maximum -ge 15) { throw "GPU not idle ($($v -join ', ') %); not starting" }
$t0 = Get-Date
"start {0:HH:mm:ss}  projection {1} h, hard cap {2} s  (GPU idle: {3} %)" -f $t0, $ProjectionH, $HardCapSec, ($v -join ", ") | Tee-Object -FilePath $log
$p = Start-Process -FilePath "pwsh" -ArgumentList @("-NoProfile", "-File", "queue_narrow.ps1", "-Run", "-OwnerOk") -NoNewWindow -PassThru `
    -RedirectStandardOutput "runs\narrow\queue.stdout" -RedirectStandardError "runs\narrow\queue.stderr"
while (-not $p.HasExited) {
    Start-Sleep -Seconds 60
    $el = ((Get-Date) - $t0).TotalSeconds
    $util = (& nvidia-smi --query-gpu=utilization.gpu,memory.used --format=csv,noheader) -join " "
    $done = @(Get-ChildItem runs\narrow\launch_*.json -ErrorAction SilentlyContinue).Count
    "checkpoint {0:F0} s ({1:F0}% of projection)  launches done {2}/6  GPU {3}" -f $el, (100 * $el / ($ProjectionH * 3600)), $done, $util | Tee-Object -FilePath $log -Append
    if ($el -ge $HardCapSec -and -not $p.HasExited) {
        "HARD CAP reached: killing the queue and its children" | Tee-Object -FilePath $log -Append
        & taskkill /PID $p.Id /T /F | Out-Null
        break
    }
}
$el = ((Get-Date) - $t0).TotalSeconds
"end {0:HH:mm:ss}  elapsed {1:F0} s ({2:F2} h)  exit {3}" -f (Get-Date), $el, ($el / 3600), $p.ExitCode | Tee-Object -FilePath $log -Append
