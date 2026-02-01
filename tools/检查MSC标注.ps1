# FormalMath MSC 标注校验脚本
# 设计文档: project/00-MSC编码标注系统设计文档-2026年2月2日.md
# 用途: 检查 Markdown 文档 Front Matter 中 msc_primary/msc_secondary 存在性与格式

param(
    [string]$Path = ".",
    [string]$Root = (Split-Path -Parent $PSScriptRoot),
    [string]$MscSubset = "project/msc/msc2020-subset.yaml",
    [switch]$Recurse
)

$checkPath = if ($Path -eq ".") { $Root } else { Join-Path $Root $Path }
$mscPath = Join-Path $Root $MscSubset

Write-Host "MSC 标注校验" -ForegroundColor Green
Write-Host "检查路径: $checkPath" -ForegroundColor Cyan
Write-Host "MSC 子集: $mscPath" -ForegroundColor Cyan

# 合法 MSC 格式：两位数 00-97，或 三位/四位数 如 20A05
$mscPattern = '^(0\d|1[0-9]|2[0-9]|3[0-9]|4[0-9]|5[0-9]|6[0-9]|7[0-9]|8[0-9]|9[0-7])([A-Z][0-9]{2,3})?$'

$stats = @{ Total = 0; WithPrimary = 0; MissingPrimary = 0; InvalidPrimary = 0; InvalidSecondary = 0; Errors = @(); Warnings = @() }
$allowedMain = @()
$allowedSub = @()
if (Test-Path $mscPath) {
    $mscContent = Get-Content -Path $mscPath -Raw -Encoding UTF8
    $allowedMain = [regex]::Matches($mscContent, '(?m)^\s+"(\d{2})":\s') | ForEach-Object { $_.Groups[1].Value }
    $allowedSub = [regex]::Matches($mscContent, '(?m)^\s+"([0-9]{2}[A-Z][0-9]{2,3})":\s') | ForEach-Object { $_.Groups[1].Value }
}

$files = Get-ChildItem -Path $checkPath -Filter "*.md" -Recurse:$Recurse -File | Where-Object { $_.FullName -notmatch "\\node_modules\\|\\ref\\" }
foreach ($f in $files) {
    $stats.Total++
    $content = Get-Content -Path $f.FullName -Raw -Encoding UTF8 -ErrorAction SilentlyContinue
    if (-not $content) { continue }

    $relPath = $f.FullName.Replace($Root + [IO.Path]::DirectorySeparatorChar, "").Replace("\", "/")
    $hasFrontMatter = $content -match '(?s)^---\r?\n(.*?)\r?\n---'
    $block = if ($hasFrontMatter) { $Matches[1] } else { "" }

    $primary = $null
    $secondary = @()
    if ($block -match 'msc_primary:\s*["\']?([^"\'\s\r\n]+)["\']?') {
        $primary = $Matches[1].Trim()
    }
    if ($block -match 'msc_secondary:\s*\r?\n?\s*-\s*["\']?([^"\'\s\r\n]+)') {
        $secondary = [regex]::Matches($block, '-\s*["\']?([^"\'\s\r\n]+)["\']?') | ForEach-Object { $_.Groups[1].Value.Trim() }
    }

    if (-not $primary) {
        $stats.MissingPrimary++
        $stats.Warnings += "$relPath : 缺少 msc_primary"
        continue
    }
    $stats.WithPrimary++

    if ($primary -notmatch $mscPattern) {
        $stats.InvalidPrimary++
        $stats.Errors += "$relPath : msc_primary 格式非法: $primary"
    }
    foreach ($s in $secondary) {
        if ($s -notmatch $mscPattern) {
            $stats.InvalidSecondary++
            $stats.Errors += "$relPath : msc_secondary 格式非法: $s"
        }
    }
}

Write-Host ""
Write-Host "统计: 总文档=$($stats.Total) 含 msc_primary=$($stats.WithPrimary) 缺 msc_primary=$($stats.MissingPrimary) 主编码非法=$($stats.InvalidPrimary) 次编码非法=$($stats.InvalidSecondary)" -ForegroundColor Cyan
foreach ($e in $stats.Errors) {
    Write-Host "  错误: $e" -ForegroundColor Red
}
foreach ($w in $stats.Warnings | Select-Object -First 20) {
    Write-Host "  警告: $w" -ForegroundColor Yellow
}
if ($stats.Warnings.Count -gt 20) {
    Write-Host "  ... 另有 $($stats.Warnings.Count - 20) 条警告" -ForegroundColor Yellow
}
if ($stats.Errors.Count -eq 0) {
    Write-Host "校验通过（无非法编码）。" -ForegroundColor Green
    exit 0
}
exit 1
