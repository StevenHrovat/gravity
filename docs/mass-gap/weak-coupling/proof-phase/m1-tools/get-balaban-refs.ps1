# Downloads the three earlier Balaban papers that the large-field papers rely on (Communications in Mathematical
# Physics, open access on Project Euclid) into this folder. Run it yourself:  pwsh -File get-balaban-refs.ps1
#   [12] Averaging operations for lattice gauge theories, CMP 98 (1985) 17-51      (how the block average behaves)
#   [14] Spaces of regular gauge field configurations ..., CMP 99 (1985) 75-102    (regularity, gauge fixing)
#   [15] The variational problem and background fields ..., CMP 102 (1985) 277-309 (minimisers; needed for M1)
# The PDFs are for reading only and are not committed (see .gitignore here).
# If the site answers with a check page instead of a PDF, the script says which ones; open those links in your
# browser and save the PDF here by hand under the same file name.

$ErrorActionPreference = "Stop"
$dir = $PSScriptRoot
$base = "https://projecteuclid.org/journals/communications-in-mathematical-physics"
$papers = [ordered]@{
    "Balaban-CMP98-1985-averaging-operations.pdf"   = "$base/volume-98/issue-1/Averaging-operations-for-lattice-gauge-theories/cmp/1103942283.pdf"
    "Balaban-CMP99-1985-regular-configurations.pdf" = "$base/volume-99/issue-1/Spaces-of-regular-gauge-field-configurations-on-a-lattice-and/cmp/1103942611.pdf"
    "Balaban-CMP102-1985-variational-problem.pdf"   = "$base/volume-102/issue-2/The-variational-problem-and-background-fields-in-renormalization-group-method/cmp/1104114383.pdf"
}

$ok = 0; $failed = @()
foreach ($name in $papers.Keys) {
    $url = $papers[$name]
    $out = Join-Path $dir $name
    Write-Host "Downloading $name ..."
    try {
        Invoke-WebRequest -Uri $url -OutFile $out
        $head = [System.IO.File]::ReadAllBytes($out) | Select-Object -First 4
        if ([System.Text.Encoding]::ASCII.GetString($head) -eq "%PDF") {
            $kb = [math]::Round((Get-Item $out).Length / 1KB)
            Write-Host "  OK ($kb KB)" -ForegroundColor Green
            $ok++
        } else {
            Remove-Item $out
            Write-Host "  Not a PDF (the site sent a page instead)" -ForegroundColor Yellow
            $failed += $url
        }
    } catch {
        Write-Host "  Failed: $($_.Exception.Message)" -ForegroundColor Yellow
        if (Test-Path $out) { Remove-Item $out }
        $failed += $url
    }
}

Write-Host ""
Write-Host "$ok of $($papers.Count) PDFs saved in $dir"
if ($failed.Count -gt 0) {
    Write-Host "Open these in your browser and save the PDF into this folder:" -ForegroundColor Yellow
    $failed | ForEach-Object { Write-Host "  $_" }
}
