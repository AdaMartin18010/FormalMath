# FormalMath项目统计空洞文档分布脚本
# 创建日期: 2025年12月31日
# 用途: 统计空洞文档在不同模块和数学家中的分布

$basePath = Split-Path -Parent $PSScriptRoot
$mathDir = Join-Path $basePath "数学家理念体系"

Write-Host "开始统计空洞文档分布..." -ForegroundColor Green

# 读取实质性内容检查报告
$contentReport = Join-Path $basePath "00-文档实质性内容检查报告-2026年01月01日.md"
$shallowFiles = @()

if (Test-Path $contentReport) {
    $reportContent = Get-Content -Path $contentReport -Raw -Encoding UTF8
    # 提取浅层文档列表
    $matches = [regex]::Matches($reportContent, '- \*\*([^\*]+)\*\*')
    foreach ($match in $matches) {
        $filePath = $match.Groups[1].Value.Trim()
        if ($filePath -match '数学家理念体系\\([^\\]+)\\([^\\]+)') {
            $mathName = $matches[0].Groups[1].Value
            $module = $matches[0].Groups[2].Value
            $shallowFiles += @{
                File = $filePath
                Mathematician = $mathName
                Module = $module
            }
        }
    }
}

# 统计分布
$distribution = @{}
$moduleDistribution = @{}
$mathDistribution = @{}

foreach ($file in $shallowFiles) {
    # 按数学家统计
    if (-not $mathDistribution.ContainsKey($file.Mathematician)) {
        $mathDistribution[$file.Mathematician] = 0
    }
    $mathDistribution[$file.Mathematician]++

    # 按模块统计
    if (-not $moduleDistribution.ContainsKey($file.Module)) {
        $moduleDistribution[$file.Module] = 0
    }
    $moduleDistribution[$file.Module]++
}

# 生成报告
$reportFile = Join-Path $basePath "00-空洞文档分布统计-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 空洞文档分布统计报告

**统计日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**统计路径**: $mathDir

---

## 📊 总体统计

| 项目 | 数量 |
|------|------|
| 总空洞文档数 | $($shallowFiles.Count) |
| 涉及数学家数 | $($mathDistribution.Count) |
| 涉及模块数 | $($moduleDistribution.Count) |

---

## 📋 按数学家分布（前20名）

"@

$sortedMath = $mathDistribution.GetEnumerator() | Sort-Object Value -Descending | Select-Object -First 20

$report += "| 排名 | 数学家 | 空洞文档数 |\n"
$report += "|------|--------|-----------|\n"

$rank = 1
foreach ($item in $sortedMath) {
    $report += "| $rank | $($item.Key) | $($item.Value) |\n"
    $rank++
}

$report += @"

---

## 📋 按模块分布

"@

$sortedModule = $moduleDistribution.GetEnumerator() | Sort-Object Value -Descending

$report += "| 模块 | 空洞文档数 |\n"
$report += "|------|-----------|\n"

foreach ($item in $sortedModule) {
    $report += "| $($item.Key) | $($item.Value) |\n"
}

$report += @"

---

## 🎯 处理优先级建议

### P0优先级（立即处理）

**数学家**:
"@

$p0Math = $sortedMath | Select-Object -First 5
foreach ($item in $p0Math) {
    $report += "- $($item.Key) ($($item.Value)个文档)\n"
}

$report += @"

**模块**:
"@

$p0Module = $sortedModule | Select-Object -First 3
foreach ($item in $p0Module) {
    $report += "- $($item.Key) ($($item.Value)个文档)\n"
}

$report += @"

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$report | Out-File -FilePath $reportFile -Encoding UTF8

Write-Host "`n统计完成!" -ForegroundColor Green
Write-Host "总空洞文档数: $($shallowFiles.Count)" -ForegroundColor Cyan
Write-Host "涉及数学家数: $($mathDistribution.Count)" -ForegroundColor Cyan
Write-Host "涉及模块数: $($moduleDistribution.Count)" -ForegroundColor Cyan
Write-Host "报告已保存到: $reportFile" -ForegroundColor Cyan
