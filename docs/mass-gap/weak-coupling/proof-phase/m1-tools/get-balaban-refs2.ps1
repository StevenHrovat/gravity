# Downloads two more Balaban papers that M1 so far cites only through Balaban's own quotations (Communications in
# Mathematical Physics, open access on Project Euclid) into this folder. Run it yourself:  pwsh -File get-balaban-refs2.ps1
#   [13] Propagators for lattice gauge theories in a background field, CMP 99 (1985) 389-434   (propagator bounds, V1 inputs)
#   [16] Ultraviolet stability of three-dimensional lattice pure gauge field theories, CMP 102 (1985) 255-275
#        (the action lower bound (71) behind the large-field factors, row R5)
# The PDFs are for reading only and are not committed (see .gitignore here).
# If the site answers with a check page instead of a PDF, the script says which ones; open those links in your
# browser and save the PDF here by hand under the same file name.

$ErrorActionPreference = "Stop"
$dir = $PSScriptRoot
$base = "https://projecteuclid.org/journals/communications-in-mathematical-physics"
$papers = [ordered]@{
    "Balaban-CMP99-1985-propagators-background-field.pdf" = "$base/volume-99/issue-3/Propagators-for-lattice-gauge-theories-in-a-background-field/cmp/1103942769.pdf"
    "Balaban-CMP102-1985-UV-stability-3D.pdf"             = "$base/volume-102/issue-2/Ultraviolet-stability-of-three-dimensional-lattice-pure-gauge-field-theories/cmp/1104114382.pdf"
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
