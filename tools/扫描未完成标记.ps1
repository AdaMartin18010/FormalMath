# FormalMath项目未完成标记扫描脚本
# 创建日期: 2025年12月31日
# 用途: 扫描所有TODO/FIXME标记，按优先级分类

$basePath = Split-Path -Parent $PSScriptRoot

Write-Host "开始扫描未完成标记..." -ForegroundColor Green

# 定义标记模式
$patterns = @{
    "TODO" = "待办事项"
    "FIXME" = "需要修复"
    "XXX" = "需要关注"
    "HACK" = "临时解决方案"
    "NOTE" = "注意事项"
    "WARNING" = "警告"
}

$allMarkers = @()
$stats = @{
    Total = 0
    ByType = @{}
    ByPriority = @{
        P0 = 0
        P1 = 0
        P2 = 0
        P3 = 0
        Unknown = 0
    }
}

# 扫描所有Markdown文件
$files = Get-ChildItem -Path $basePath -Filter "*.md" -Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak)"
    }

foreach ($file in $files) {
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8
    $lines = Get-Content -Path $file.FullName -Encoding UTF8

    foreach ($pattern in $patterns.Keys) {
        $matches = [regex]::Matches($content, "$pattern[:\s]+(.+?)(?:\n|$)", [System.Text.RegularExpressions.RegexOptions]::Multiline -bor [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)

        foreach ($match in $matches) {
            $markerText = $match.Groups[1].Value.Trim()
            $lineNum = ($content.Substring(0, $match.Index) -split "`n").Count

            # 尝试识别优先级
            $priority = "Unknown"
            if ($markerText -match "P0|核心|基础|立即") {
                $priority = "P0"
            } elseif ($markerText -match "P1|重要|常用") {
                $priority = "P1"
            } elseif ($markerText -match "P2|扩展|应用") {
                $priority = "P2"
            } elseif ($markerText -match "P3|可选|补充") {
                $priority = "P3"
            }

            $relativePath = $file.FullName.Replace($basePath, "").TrimStart('\')

            $marker = [PSCustomObject]@{
                File = $relativePath
                Line = $lineNum
                Type = $pattern
                Text = $markerText
                Priority = $priority
                FullPath = $file.FullName
            }

            $allMarkers += $marker
            $stats.Total++

            if (-not $stats.ByType.ContainsKey($pattern)) {
                $stats.ByType[$pattern] = 0
            }
            $stats.ByType[$pattern]++

            $stats.ByPriority[$priority]++
        }
    }
}

# 输出统计信息
Write-Host "`n扫描完成!" -ForegroundColor Green
Write-Host "总标记数: $($stats.Total)" -ForegroundColor Cyan
Write-Host "`n按类型统计:" -ForegroundColor Yellow
foreach ($type in $stats.ByType.Keys | Sort-Object) {
    Write-Host "  $type`: $($stats.ByType[$type])" -ForegroundColor Cyan
}

Write-Host "`n按优先级统计:" -ForegroundColor Yellow
Write-Host "  P0 (核心): $($stats.ByPriority.P0)" -ForegroundColor Red
Write-Host "  P1 (重要): $($stats.ByPriority.P1)" -ForegroundColor Yellow
Write-Host "  P2 (扩展): $($stats.ByPriority.P2)" -ForegroundColor Cyan
Write-Host "  P3 (可选): $($stats.ByPriority.P3)" -ForegroundColor Green
Write-Host "  未知: $($stats.ByPriority.Unknown)" -ForegroundColor Gray

# 生成报告文件
$reportFile = Join-Path $basePath "00-未完成标记扫描报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 未完成标记扫描报告

**扫描日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**扫描路径**: $basePath

## 📊 统计信息

| 项目 | 数量 |
|------|------|
| 总标记数 | $($stats.Total) |
| P0 (核心) | $($stats.ByPriority.P0) |
| P1 (重要) | $($stats.ByPriority.P1) |
| P2 (扩展) | $($stats.ByPriority.P2) |
| P3 (可选) | $($stats.ByPriority.P3) |
| 未知优先级 | $($stats.ByPriority.Unknown) |

## 📝 按类型统计

"@

foreach ($type in $stats.ByType.Keys | Sort-Object) {
    $typeName = $patterns[$type]
    $report += "| $type ($typeName) | $($stats.ByType[$type]) |`n"
}

$report += @"

## 🎯 P0优先级标记列表（核心概念、基础理论）

"@

$p0Markers = $allMarkers | Where-Object { $_.Priority -eq "P0" }
if ($p0Markers.Count -gt 0) {
    foreach ($marker in $p0Markers) {
        $report += "### $($marker.File) (第$($marker.Line)行)`n`n"
        $report += "- **类型**: $($marker.Type)`n"
        $report += "- **内容**: $($marker.Text)`n`n"
    }
} else {
    $report += "暂无P0优先级标记。`n`n"
}

$report += @"

## 📋 P1优先级标记列表（重要内容、常用概念）

"@

$p1Markers = $allMarkers | Where-Object { $_.Priority -eq "P1" }
if ($p1Markers.Count -gt 0) {
    foreach ($marker in $p1Markers | Select-Object -First 20) {
        $report += "- **$($marker.File)** (第$($marker.Line)行): $($marker.Text)`n"
    }
    if ($p1Markers.Count -gt 20) {
        $report += "`n... 还有 $($p1Markers.Count - 20) 个P1标记`n"
    }
} else {
    $report += "暂无P1优先级标记。`n`n"
}

$report += @"

## 📋 完整标记列表

"@

foreach ($marker in $allMarkers | Sort-Object Priority, File, Line) {
    $report += "- **[P$($marker.Priority)]** `$($marker.File)` (第$($marker.Line)行): $($marker.Type) - $($marker.Text)`n"
}

$report | Out-File -FilePath $reportFile -Encoding UTF8
Write-Host "`n报告已保存到: $reportFile" -ForegroundColor Cyan

# 生成CSV文件（便于处理）
$csvFile = Join-Path $basePath "00-未完成标记列表-$(Get-Date -Format 'yyyy年MM月dd日').csv"
$allMarkers | Export-Csv -Path $csvFile -Encoding UTF8 -NoTypeInformation
Write-Host "CSV列表已保存到: $csvFile" -ForegroundColor Cyan
