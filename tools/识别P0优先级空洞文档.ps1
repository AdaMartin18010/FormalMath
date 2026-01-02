# FormalMath项目识别P0优先级空洞文档脚本
# 创建日期: 2026年01月01日
# 用途: 识别P0级数学家的空洞文档，优先补充

$basePath = Split-Path -Parent $PSScriptRoot
$mathDir = Join-Path $basePath "数学家理念体系"

Write-Host "开始识别P0优先级空洞文档..." -ForegroundColor Green

# P0级数学家列表
$p0Mathematicians = @(
    "希尔伯特数学理念",
    "黎曼数学理念",
    "庞加莱数学理念",
    "格洛腾迪克数学理念"
)

# 优先级模块
$priorityModules = @(
    "01-核心理论",
    "02-数学内容深度分析"
)

# 读取实质性内容检查报告
$contentReport = Join-Path $basePath "00-文档实质性内容检查报告-2026年01月01日.md"
$shallowFiles = @()

if (Test-Path $contentReport) {
    $reportContent = Get-Content -Path $contentReport -Raw -Encoding UTF8

    # 提取浅层文档列表
    $pattern = '- \*\*数学家理念体系\\([^\\]+)\\([^\\]+)\\([^\*]+)\*\*'
    $matches = [regex]::Matches($reportContent, $pattern)

    foreach ($match in $matches) {
        $mathName = $match.Groups[1].Value.Trim()
        $module = $match.Groups[2].Value.Trim()
        $filePath = $match.Groups[0].Value -replace '^- \*\*', '' -replace '\*\*$', ''

        # 检查是否是P0级数学家
        $isP0 = $false
        foreach ($p0Math in $p0Mathematicians) {
            if ($mathName -eq $p0Math) {
                $isP0 = $true
                break
            }
        }

        # 检查是否是优先级模块
        $isPriorityModule = $false
        foreach ($priorityModule in $priorityModules) {
            if ($module -eq $priorityModule) {
                $isPriorityModule = $true
                break
            }
        }

        if ($isP0 -and $isPriorityModule) {
            $shallowFiles += @{
                File = $filePath
                Mathematician = $mathName
                Module = $module
                Priority = "P0"
            }
        }
    }
}

# 按数学家和模块分组
$grouped = @{}
foreach ($file in $shallowFiles) {
    $key = "$($file.Mathematician)|$($file.Module)"
    if (-not $grouped.ContainsKey($key)) {
        $grouped[$key] = @()
    }
    $grouped[$key] += $file
}

# 生成报告
$reportFile = Join-Path $basePath "00-P0优先级空洞文档列表-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# P0优先级空洞文档列表

**生成日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**优先级**: P0（最高优先级）
**目标**: 优先补充这些文档的实质性内容

---

## 📊 统计信息

| 项目 | 数量 |
|------|------|
| **P0级数学家数** | $($p0Mathematicians.Count) |
| **P0优先级空洞文档** | $($shallowFiles.Count) |
| **涉及模块数** | $($grouped.Count) |

---

## 📋 P0优先级空洞文档列表

### 按数学家和模块分组

"@

foreach ($p0Math in $p0Mathematicians) {
    $report += "### $p0Math`n`n"

    foreach ($priorityModule in $priorityModules) {
        $key = "$p0Math|$priorityModule"
        if ($grouped.ContainsKey($key)) {
            $files = $grouped[$key]
            $report += "#### $priorityModule ($($files.Count)个文档)`n`n"

            foreach ($file in $files) {
                $report += "- **$($file.File)**`n"
            }
            $report += "`n"
        }
    }
}

$report += @"

---

## 🎯 补充优先级

### P0-1（最高优先级）

**希尔伯特数学理念 - 01-核心理论**
- 立即补充，作为示例文档

### P0-2（高优先级）

**黎曼数学理念 - 01-核心理论**
**庞加莱数学理念 - 01-核心理论**
**格洛腾迪克数学理念 - 01-核心理论**

### P0-3（中优先级）

**所有P0级数学家 - 02-数学内容深度分析**

---

## 📝 补充要求

每个文档必须包含：
- ✅ 字数: ≥1000字（核心理论文档）
- ✅ 数学公式: ≥3-5个LaTeX公式
- ✅ 例子: ≥3-5个具体例子
- ✅ 历史背景和应用实例
- ✅ 参考文献

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$report | Out-File -FilePath $reportFile -Encoding UTF8

Write-Host "`n识别完成!" -ForegroundColor Green
Write-Host "P0级数学家数: $($p0Mathematicians.Count)" -ForegroundColor Cyan
Write-Host "P0优先级空洞文档: $($shallowFiles.Count)" -ForegroundColor Yellow
Write-Host "涉及模块数: $($grouped.Count)" -ForegroundColor Cyan
Write-Host "报告已保存到: $reportFile" -ForegroundColor Cyan
