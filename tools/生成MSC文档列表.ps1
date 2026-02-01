# FormalMath MSC 按编码生成文档列表
# 设计文档: project/00-MSC编码标注系统设计文档-2026年2月2日.md
# 用途: 扫描 Markdown 文档 Front Matter 中的 msc_primary，按编码分组输出文档列表与简单统计

param(
    [string]$Root = (Split-Path -Parent $PSScriptRoot),
    [switch]$ReportOnly,
    [switch]$All
)

$Root = (Resolve-Path $Root).Path
$outDir = Join-Path $Root "project\msc"
$listByCode = @{}
$allWithPrimary = @()

# 默认只扫描已标注 MSC 的目录，-All 时扫描全项目
$scanPaths = if ($All) { @($Root) } else {
    @("concept", "docs\00-核心概念理解三问\11-核心定理多表征", "project\msc", "数学家理念体系") | ForEach-Object {
        $p = Join-Path $Root $_
        if (Test-Path $p) { $p }
    }
    if ($scanPaths.Count -eq 0) { @($Root) }
}

$files = $scanPaths | ForEach-Object { Get-ChildItem -Path $_ -Filter "*.md" -Recurse -File -ErrorAction SilentlyContinue } | Where-Object {
    $_.FullName -notmatch "\\node_modules\\|\\ref\\|\\mcps\\"
} | Sort-Object -Property FullName -Unique

$files | ForEach-Object {
    $content = Get-Content -Path $_.FullName -Raw -Encoding UTF8 -ErrorAction SilentlyContinue
    if (-not $content) { return }
    $relPath = $_.FullName.Replace($Root + [IO.Path]::DirectorySeparatorChar, "").Replace("\", "/")
    if (-not ($content -match '(?s)^---\r?\n(.*?)\r?\n---')) { return }
    $block = $Matches[1]
    if (-not $block -or -not ($block -match 'msc_primary:\s*(\S+)')) { return }
    $primary = $Matches[1].Trim().Trim('"').Trim("'")
    if (-not $primary) { return }
    if (-not $listByCode.ContainsKey($primary)) { $listByCode[$primary] = @() }
    $listByCode[$primary] += $relPath
    $allWithPrimary += [PSCustomObject]@{ Primary = $primary; Path = $relPath }
}

# 按主编码排序输出
$sortedCodes = $listByCode.Keys | Sort-Object
$report = @()
$report += "# MSC 按编码文档列表（自动生成）"
$report += ""
$report += "**生成时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm')"
$report += "**说明**: 由 `tools/生成MSC文档列表.ps1` 扫描项目 .md 文件 Front Matter 中的 msc_primary 生成。"
$report += ""
$report += "---"
$report += ""

foreach ($code in $sortedCodes) {
    $report += "## $code ($($listByCode[$code].Count) 篇)"
    $report += ""
    foreach ($path in ($listByCode[$code] | Sort-Object)) {
        $report += "- $path"
    }
    $report += ""
}

$report += "---"
$report += "## 统计摘要"
$report += ""
$report += "| 主编码 | 文档数 |"
$report += "|--------|--------|"
$byMain = @{}
foreach ($p in $allWithPrimary) {
    $m = if ($p.Primary -match '^(\d{2})') { $Matches[1] } else { "other" }
    if (-not $byMain.ContainsKey($m)) { $byMain[$m] = 0 }
    $byMain[$m]++
}
foreach ($m in ($byMain.Keys | Sort-Object)) {
    $report += "| $m | $($byMain[$m]) |"
}
$report += ""
$report += "**合计**: $($allWithPrimary.Count) 篇文档含 msc_primary。"
$report += ""

$reportText = $report -join "`n"
if (-not $ReportOnly) {
    $outFile = Join-Path $outDir "msc-doc-list-generated.md"
    Set-Content -Path $outFile -Value $reportText -Encoding UTF8 -NoNewline
    Write-Host "已写入: $outFile" -ForegroundColor Green
}
Write-Host "统计: 共 $($allWithPrimary.Count) 篇文档含 msc_primary，按 $($listByCode.Count) 个编码分组。" -ForegroundColor Cyan
$reportText
