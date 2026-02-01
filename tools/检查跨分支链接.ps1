# FormalMath 跨分支链接校验脚本
# 设计文档: project/00-跨分支链接系统设计文档-2026年2月2日.md
# 用途: 校验 cross-branch-links.yaml 中路径存在性、必填字段、重复项

param(
    [string]$LinksFile = "project/links/cross-branch-links.yaml",
    [string]$Root = (Split-Path -Parent $PSScriptRoot)
)

$linksPath = Join-Path $Root $LinksFile
if (-not (Test-Path $linksPath)) {
    Write-Host "未找到链接文件: $linksPath" -ForegroundColor Red
    exit 1
}

Write-Host "跨分支链接校验" -ForegroundColor Green
Write-Host "链接文件: $linksPath" -ForegroundColor Cyan
Write-Host "项目根: $Root" -ForegroundColor Cyan

$content = Get-Content -Path $linksPath -Raw -Encoding UTF8
$stats = @{ Total = 0; Valid = 0; MissingSource = 0; MissingTarget = 0; Duplicate = 0; MissingField = 0; Errors = @() }

# 简单解析 YAML links 块（不依赖外部库）
$inLinks = $false
$links = @()
$current = @{}
foreach ($line in ($content -split "`n")) {
    if ($line -match "^\s*links:\s*$") { $inLinks = $true; continue }
    if ($inLinks -and $line -match "^\s+-\s+id:\s*(.+)") {
        if ($current.Count -gt 0) { $links += $current.Clone() }
        $current = @{ id = $matches[1].Trim() }
        continue
    }
    if ($inLinks -and $current.Count -gt 0) {
        if ($line -match "^\s+(\w+):\s*(.+)") {
            $current[$matches[1]] = $matches[2].Trim().Trim('"')
        }
        if ($line -match "^\s+(\w+):\s*$") { $current[$matches[1]] = "" }
    }
}
if ($current.Count -gt 0) { $links += $current }

# 若简单解析失败，尝试按 id/source/target 提取
if ($links.Count -eq 0) {
    $idMatches = [regex]::Matches($content, '(?m)^\s+-\s+id:\s*(.+)$')
    $srcMatches = [regex]::Matches($content, '(?m)^\s+source:\s*["]?([^"\s#]+)["]?\s*')
    $tgtMatches = [regex]::Matches($content, '(?m)^\s+target:\s*["]?([^"\s#]+)["]?\s*')
    $maxN = [Math]::Max($idMatches.Count, [Math]::Max($srcMatches.Count, $tgtMatches.Count))
    for ($i = 0; $i -lt $maxN; $i++) {
        $links += @{
            id     = if ($i -lt $idMatches.Count) { $idMatches[$i].Groups[1].Value.Trim() } else { "L$($i+1)" }
            source = if ($i -lt $srcMatches.Count) { $srcMatches[$i].Groups[1].Value.Trim() } else { "" }
            target = if ($i -lt $tgtMatches.Count) { $tgtMatches[$i].Groups[1].Value.Trim() } else { "" }
        }
    }
}

$stats.Total = $links.Count
$seen = @{}
foreach ($l in $links) {
    $src = if ($l.source) { $l.source } else { "" }
    $tgt = if ($l.target) { $l.target } else { "" }
    if (-not $src -or -not $tgt) {
        $stats.MissingField++
        $stats.Errors += "链接 $($l.id): 缺少 source 或 target"
        continue
    }
    $key = "$src|$tgt"
    if ($seen[$key]) {
        $stats.Duplicate++
        $stats.Errors += "链接 $($l.id): 与 $($seen[$key]) 重复 (source-target)"
    }
    $seen[$key] = $l.id

    $srcFull = Join-Path $Root $src
    $tgtFull = Join-Path $Root $tgt
    if (-not (Test-Path $srcFull)) {
        $stats.MissingSource++
        $stats.Errors += "链接 $($l.id): 源路径不存在: $src"
    }
    if (-not (Test-Path $tgtFull)) {
        $stats.MissingTarget++
        $stats.Errors += "链接 $($l.id): 目标路径不存在: $tgt"
    }
    if ((Test-Path $srcFull) -and (Test-Path $tgtFull)) {
        $stats.Valid++
    }
}

Write-Host ""
Write-Host "统计: 总链接数=$($stats.Total) 路径有效=$($stats.Valid) 源缺失=$($stats.MissingSource) 目标缺失=$($stats.MissingTarget) 重复=$($stats.Duplicate) 缺字段=$($stats.MissingField)" -ForegroundColor Cyan
foreach ($e in $stats.Errors) {
    Write-Host "  $e" -ForegroundColor Yellow
}
if ($stats.Errors.Count -eq 0) {
    Write-Host "校验通过。" -ForegroundColor Green
    exit 0
}
exit 1
