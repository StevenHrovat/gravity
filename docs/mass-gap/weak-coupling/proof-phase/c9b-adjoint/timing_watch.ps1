# c9b GPU timing job with a hard-cap watcher (TIMING.md). Run ONLY in a GPU slot assigned by the coordinator, after the CPU pilot passed.
#   pwsh -File timing_watch.ps1 [-CapSeconds 1800] [-EstimateSeconds 1700] [-DryRun]
# -DryRun checks the GPU and prints the command without starting anything.
param(
    [int]$CapSeconds = 1800,
    [int]$EstimateSeconds = 1700,
    [int]$PollSeconds = 15,
    [switch]$DryRun
)
$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot
$log = Join-Path $PSScriptRoot 'timing_watch.log'
function Log([string]$m) { $line = "{0:u} {1}" -f (Get-Date), $m; Write-Output $line; Add-Content -Path $log -Value $line }

# 1. GPU must be free
$util = [int](nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits).Trim()
$apps = @(nvidia-smi --query-compute-apps=pid,used_memory --format=csv,noheader | Where-Object { $_ -match '\d' -and $_ -notmatch 'N/A' })
Log "GPU utilisation $util %; compute processes holding memory: $($apps.Count)"
if ($util -gt 20 -or $apps.Count -gt 0) { Log 'ABORT: GPU not free'; exit 3 }

$python = (& py -c "import sys; print(sys.executable)").Trim()
$jobArgs = @('ir_constrained.py', 'timing', '--go', '--gpu', '--beta', '2.3', '--N', '40', '--n', '3', '--w', '2.0', '--kappa', '200',
    '--R', '2', '--B', '1', '--x', '0,0,0,0,1', '--npre', '200', '--eps', '0.05', '--nleap', '10', '--tune-traj', '10',
    '--tune-max', '6', '--seed', '31', '--bgseed', '3000', '--max-wall', '1680',
    '--progress', 'timing_progress.jsonl', '--out', 'timing_job.npz')
Log ("command: " + $python + ' ' + ($jobArgs -join ' '))
if ($DryRun) { Log 'dry run: nothing started'; exit 0 }

# 2. start the job
$p = Start-Process -FilePath $python -ArgumentList $jobArgs -PassThru -NoNewWindow `
    -RedirectStandardOutput 'timing_job.out' -RedirectStandardError 'timing_job.err'
$t0 = Get-Date
Log "started PID $($p.Id); cap $CapSeconds s; estimate $EstimateSeconds s"

# 3./4. poll, compare with the estimate, kill at the cap whatever the job says
while (-not $p.HasExited) {
    Start-Sleep -Seconds $PollSeconds
    $el = [int]((Get-Date) - $t0).TotalSeconds
    $last = if (Test-Path 'timing_progress.jsonl') { Get-Content 'timing_progress.jsonl' -Tail 1 } else { '(no progress yet)' }
    $flag = if ($el -gt $EstimateSeconds) { ' OVER ESTIMATE' } else { '' }
    Log "elapsed $el s / estimate $EstimateSeconds s / cap $CapSeconds s$flag | $last"
    if ($el -ge $CapSeconds) {
        Log "CAP REACHED: killing PID $($p.Id) and its children"
        & taskkill /PID $p.Id /T /F | Out-Null
        Start-Sleep -Seconds 3
        Log "killed; exited: $($p.HasExited)"
        break
    }
}
$el = [int]((Get-Date) - $t0).TotalSeconds
Log "job ended after $el s; exit code: $(if ($p.HasExited) { $p.ExitCode } else { 'killed' })"
if (Test-Path 'timing_job.out') { Get-Content 'timing_job.out' -Tail 3 | ForEach-Object { Log "job: $_" } }
