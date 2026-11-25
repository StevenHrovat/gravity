# Downloads Balaban's five lattice-gauge papers (Communications in Mathematical Physics, free on Project Euclid)
# into this folder. Run it yourself:  pwsh -File get-balaban.ps1
# The PDFs are for reading only and are not committed (see .gitignore here).
# If the site answers with a check page instead of a PDF, the script says which ones; open those links in your
# browser and save the PDF here by hand under the same file name.

$ErrorActionPreference = "Stop"
$dir = $PSScriptRoot
$base = "https://projecteuclid.org/journals/communications-in-mathematical-physics"
$papers = [ordered]@{
    "Balaban-CMP109-1987-RG-I-generation.pdf"        = "$base/volume-109/issue-2/Renormalization-group-approach-to-lattice-gauge-field-theories-I-Generation/cmp/1104116842.pdf"
    "Balaban-CMP116-1988-RG-II-cluster.pdf"          = "$base/volume-116/issue-1/Renormalization-group-approach-to-lattice-gauge-field-theories-II-Cluster/cmp/1104161193.pdf"
    "Balaban-CMP119-1988-convergent-expansions.pdf"  = "$base/volume-119/issue-2/Convergent-renormalization-expansions-for-lattice-gauge-theories/cmp/1104162401.pdf"
    "Balaban-CMP122-1989-large-field-I.pdf"          = "$base/volume-122/issue-2/Large-field-renormalization-I-The-basic-step-of-the-bf/cmp/1104178393.pdf"
    "Balaban-CMP122-1989-large-field-II.pdf"         = "$base/volume-122/issue-3/Large-field-renormalization-II-Localization-exponentiation-and-bounds-for-the/cmp/1104178467.pdf"
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
