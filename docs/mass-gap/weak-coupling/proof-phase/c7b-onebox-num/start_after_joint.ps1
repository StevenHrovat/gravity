# Coordinator: start the one-box queue (Tier 1) once the joint z0/z_e queue has finished (its log ends with JOINT DONE,
# or its queue process is gone), so the two never share the GPU.
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$jlog = "../c5e-dmp/runs-gpu/queue_joint.log"
New-Item -ItemType Directory -Force runs | Out-Null
"WAITING for the joint queue $(Get-Date -Format s)" | Add-Content runs/queue_onebox.log
while ($true) {
    $done = (Test-Path $jlog) -and (Select-String -Path $jlog -Pattern '^JOINT DONE' -Quiet)
    $alive = Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match 'queue_joint_gpu|run_su2_gpu' }
    if ($done -or -not $alive) { break }
    Start-Sleep 60
}
Start-Sleep 30
& pwsh -NoProfile -File (Join-Path $PSScriptRoot "queue_onebox_gpu.ps1") -Tier 1
