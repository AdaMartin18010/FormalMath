# Requires: Pandoc 3.x, XeLaTeX (for PDF) optional
# Usage: powershell -ExecutionPolicy Bypass -File scripts/export.ps1

$ErrorActionPreference = "Stop"

$src = "docs/04-几何学/07-欧氏与非欧几何的射影视角-形式论证.md"
$outDir = "out"

if (-not (Test-Path $outDir)) { New-Item -ItemType Directory -Force -Path $outDir | Out-Null }

Write-Host "[1/3] Export HTML"
pandoc $src --from gfm --to html5 --metadata title="欧氏与非欧几何的射影视角" --toc --toc-depth=3 --standalone -o "$outDir/ck-geometry.html"

Write-Host "[2/3] Export PDF (XeLaTeX)"
try {
    pandoc $src --from gfm --pdf-engine=xelatex -V CJKmainfont="Microsoft YaHei" -V geometry:margin=1in --toc --toc-depth=3 -o "$outDir/ck-geometry.pdf"
} catch {
    Write-Warning "PDF 导出失败：请确认已安装 XeLaTeX（MiKTeX/TeX Live）。"
}

Write-Host "[3/3] Export DOCX"
pandoc $src --from gfm --toc --toc-depth=3 -o "$outDir/ck-geometry.docx"

Write-Host "导出完成：$outDir" 