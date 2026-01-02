# FormalMath项目识别明显模板文档脚本
# 创建日期: 2026年01月01日
# 用途: 识别明显是模板的文档（基于模板文字模式）

$basePath = Split-Path -Parent $PSScriptRoot
$mathDir = Join-Path $basePath "数学家理念体系"

Write-Host "开始识别明显模板文档..." -ForegroundColor Green

# 模板文字模式（必须包含3个或更多才算模板）
$templatePatterns = @(
    '在数学和科学的多个领域都有重要应用',
    '从理论物理到工程实践，这一理论都发挥着重要作用',
    '该应用的核心要点和意义',
    '体现了.*对数学的深刻洞察和创新思维',
    '这一理论在数学史上占有重要地位',
    '对数学发展产生了深远影响',
    '不仅解决了当时的数学问题，而且为后续的数学研究提供了重要的理论基础',
    '待补充|TODO|待完善|待完成|待添加',
    '关联的意义|方法的关联分析|关联的结构|关联的影响'
)

$results = @{
    TotalFiles = 0
    TemplateFiles = @()
}

# 检查单个文件
function Test-TemplateDocument {
    param([string]$FilePath)

    try {
        $content = Get-Content -Path $FilePath -Raw -Encoding UTF8 -ErrorAction Stop

        if ([string]::IsNullOrWhiteSpace($content)) {
            return @{ IsTemplate = $true; Reason = "文件为空"; PatternCount = 0 }
        }

        # 计算字数
        $chineseChars = ([regex]::Matches($content, "[\u4e00-\u9fa5]")).Count
        $englishWords = ([regex]::Matches($content, "\b[a-zA-Z]{2,}\b")).Count
        $wordCount = $chineseChars + $englishWords

        # 检查模板模式
        $patternCount = 0
        $matchedPatterns = @()

        foreach ($pattern in $templatePatterns) {
            if ($content -match $pattern) {
                $patternCount++
                $matchedPatterns += $pattern
            }
        }

        # 如果包含3个或更多模板模式，认为是明显模板文档
        if ($patternCount -ge 3) {
            return @{
                IsTemplate = $true
                Reason = "包含$patternCount个模板模式"
                PatternCount = $patternCount
                MatchedPatterns = $matchedPatterns
                WordCount = $wordCount
            }
        }

        # 如果字数少于300且包含模板模式，也认为是模板
        if ($wordCount -lt 300 -and $patternCount -ge 1) {
            return @{
                IsTemplate = $true
                Reason = "字数少($wordCount)且包含模板模式($patternCount个)"
                PatternCount = $patternCount
                MatchedPatterns = $matchedPatterns
                WordCount = $wordCount
            }
        }

        return @{ IsTemplate = $false; Reason = "通过"; PatternCount = $patternCount; WordCount = $wordCount }
    }
    catch {
        return @{ IsTemplate = $false; Reason = "读取错误"; PatternCount = 0; WordCount = 0 }
    }
}

# 扫描所有Markdown文件
$mdFiles = Get-ChildItem -Path $mathDir -Filter "*.md" -Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak)" -and
        $_.Name -notmatch "^00-"
    }

$results.TotalFiles = $mdFiles.Count
$processed = 0

foreach ($file in $mdFiles) {
    $processed++
    if ($processed % 100 -eq 0) {
        Write-Host "已处理: $processed / $($results.TotalFiles)" -ForegroundColor Gray
    }

    $relativePath = $file.FullName.Replace($basePath + "\", "")
    $checkResult = Test-TemplateDocument -FilePath $file.FullName

    if ($checkResult.IsTemplate) {
        $results.TemplateFiles += @{
            File = $relativePath
            Reason = $checkResult.Reason
            PatternCount = $checkResult.PatternCount
            WordCount = $checkResult.WordCount
            MatchedPatterns = $checkResult.MatchedPatterns
        }
    }
}

# 生成报告
$reportFile = Join-Path $basePath "00-明显模板文档列表-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 明显模板文档列表

**识别日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**识别路径**: $mathDir

---

## 📊 统计信息

| 项目 | 数量 |
|------|------|
| 总文档数 | $($results.TotalFiles) |
| 明显模板文档 | $($results.TemplateFiles.Count) |
| 模板文档比例 | $([math]::Round($results.TemplateFiles.Count / $results.TotalFiles * 100, 1))% |

---

## 📝 明显模板文档列表（$($results.TemplateFiles.Count)个）

"@

# 按模板模式数量排序
$sortedTemplates = $results.TemplateFiles | Sort-Object -Property PatternCount -Descending | Sort-Object -Property WordCount

foreach ($item in $sortedTemplates) {
    $report += "### $($item.File)`n`n"
    $report += "- **原因**: $($item.Reason)`n"
    $report += "- **字数**: $($item.WordCount)`n"
    $report += "- **模板模式数**: $($item.PatternCount)`n"
    if ($item.MatchedPatterns.Count -gt 0) {
        $report += "- **匹配的模式**: `n"
        foreach ($pattern in ($item.MatchedPatterns | Select-Object -First 3)) {
            $report += "  - $pattern`n"
        }
    }
    $report += "`n"
}

$report += @"

---

## 🎯 处理建议

### 优先级分类

**P0（立即删除）**: 包含5个或更多模板模式的文档
**P1（高优先级）**: 包含3-4个模板模式的文档
**P2（中优先级）**: 字数少于300且包含模板模式的文档

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$report | Out-File -FilePath $reportFile -Encoding UTF8

Write-Host "`n识别完成!" -ForegroundColor Green
Write-Host "总文档数: $($results.TotalFiles)" -ForegroundColor Cyan
Write-Host "明显模板文档: $($results.TemplateFiles.Count)" -ForegroundColor Yellow
Write-Host "报告已保存到: $reportFile" -ForegroundColor Cyan
