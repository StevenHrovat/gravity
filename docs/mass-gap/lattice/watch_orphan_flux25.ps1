# One-off (2026-11-21): the run su2_b2.5_l15_flux was started by the old GPU coordinator just before the reorder and kept running after
# it was stopped. Wait for it to end and log its completion in the same format, so queue_boundary_gpu2.ps1 skips it instead of rerunning it.
Set-Location $PSScriptRoot
$out = "runs-gpu/boundary"; $qlog = "$out/queue_boundary.log"; $t = Get-Date
while (Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match 'boundary\.py run su2 2\.5 15 flux' }) { Start-Sleep 30 }
$ok = Select-String -Path "$out/su2_b2.5_l15_flux.log" -Pattern "^done " -Quiet
$code = if ($ok) { 0 } else { 1 }
"su2_b2.5_l15_flux (gpu, attempt 1) exit $code minutes $([int]((Get-Date) - $t).TotalMinutes)+ (started by the old coordinator, completion logged by watch_orphan_flux25.ps1)" | Add-Content $qlog
