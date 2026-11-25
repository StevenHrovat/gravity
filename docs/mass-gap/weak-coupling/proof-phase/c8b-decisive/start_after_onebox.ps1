# Coordinator: start the decisive queue (Tier 1) once the one-box queue has finished (its log ends with ONEBOX DONE,
# or its queue process is gone), so the two never share the GPU.
$ErrorActionPreference = "Continue"
Set-Location $PSScriptRoot
$olog = "../c7b-onebox-num/runs/queue_onebox.log"
New-Item -ItemType Directory -Force runs | Out-Null
"WAITING for the one-box queue $(Get-Date -Format s)" | Add-Content runs/queue_decisive.log
while ($true) {
    $done = (Test-Path $olog) -and (Select-String -Path $olog -Pattern 'ONEBOX DONE' -Quiet)
    $alive = Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match 'queue_onebox_gpu' }
    if ($done -or -not $alive) { break }
    Start-Sleep 60
}
Start-Sleep 30
& pwsh -NoProfile -File (Join-Path $PSScriptRoot "queue_decisive_gpu.ps1") -Tier 1
