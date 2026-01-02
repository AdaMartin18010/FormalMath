# FormalMath项目检查文档实质性内容脚本
# 创建日期: 2025年12月31日
# 用途: 检查文档是否有实质性内容

$basePath = Split-Path -Parent $PSScriptRoot
$mathDir = Join-Path $basePath "数学家理念体系"

Write-Host "开始检查文档实质性内容..." -ForegroundColor Green

# 实质性内容的判断标准
$minWordCount = 500  # 最小字数
$minMathFormulas = 1  # 最小数学公式数
$minExamples = 1  # 最小例子数
$minCodeBlocks = 0  # 最小代码块数（可选）

$results = @{
    TotalFiles = 0
    SubstantialFiles = 0
    EmptyFiles = 0
    ShallowFiles = @()
    EmptyContentFiles = @()
}

# 检查单个文件
function Test-SubstantialContent {
    param(
        [string]$FilePath,
        [string]$RelativePath
    )

    if (-not (Test-Path $FilePath)) {
        return @{
            IsSubstantial = $false
            Reason = "文件不存在"
            WordCount = 0
            MathFormulas = 0
            Examples = 0
            CodeBlocks = 0
        }
    }

    try {
        $content = Get-Content -Path $FilePath -Raw -Encoding UTF8 -ErrorAction Stop

        if ([string]::IsNullOrWhiteSpace($content)) {
            return @{
                IsSubstantial = $false
                Reason = "文件为空"
                WordCount = 0
                MathFormulas = 0
                Examples = 0
                CodeBlocks = 0
            }
        }

        # 计算字数（中文字符 + 英文单词）
        $chineseChars = ([regex]::Matches($content, "[\u4e00-\u9fa5]")).Count
        $englishWords = ([regex]::Matches($content, "\b[a-zA-Z]{2,}\b")).Count
        $wordCount = $chineseChars + $englishWords

        # 检查数学公式（LaTeX格式）
        $mathFormulas = ([regex]::Matches($content, '\$[^\$]+\$|\\\[.*?\\\]|\\\(.*?\\\)')).Count

        # 检查例子（包含"例子"、"示例"、"Example"等关键词）
        $examplePattern = '(例子|示例|Example|example|实例|案例|Case|case)'
        $examples = ([regex]::Matches($content, $examplePattern, [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)).Count

        # 检查代码块
        $codeBlocks = ([regex]::Matches($content, '```')).Count / 2

        # 检查是否只是模板或占位符
        $isTemplate = $content -match '(待补充|TODO|待完善|待完成|待添加|placeholder|template|模板|占位符)'

        # 检查是否只有标题和空行
        $lines = $content -split "`n" | Where-Object { $_.Trim() -ne "" -and $_ -notmatch '^#{1,6}\s' }
        $hasContent = $lines.Count -gt 3

        # 判断是否有实质性内容
        $isSubstantial = $true
        $reasons = @()

        if ($wordCount -lt $minWordCount) {
            $isSubstantial = $false
            $reasons += "字数不足($wordCount < $minWordCount)"
        }

        if ($mathFormulas -lt $minMathFormulas -and $RelativePath -match '数学内容|核心理论|理论') {
            $isSubstantial = $false
            $reasons += "数学公式不足($mathFormulas < $minMathFormulas)"
        }

        if ($isTemplate) {
            $isSubstantial = $false
            $reasons += "包含模板标记"
        }

        if (-not $hasContent) {
            $isSubstantial = $false
            $reasons += "只有标题无内容"
        }

        # 检查是否只有目录结构
        $onlyHeaders = ($content -match '^#{1,6}\s') -and ($wordCount -lt 200)
        if ($onlyHeaders) {
            $isSubstantial = $false
            $reasons += "只有目录结构"
        }

        return @{
            IsSubstantial = $isSubstantial
            Reason = if ($reasons.Count -gt 0) { $reasons -join ", " } else { "通过" }
            WordCount = $wordCount
            MathFormulas = $mathFormulas
            Examples = $examples
            CodeBlocks = $codeBlocks
            IsTemplate = $isTemplate
            HasContent = $hasContent
        }
    }
    catch {
        return @{
            IsSubstantial = $false
            Reason = "读取错误: $($_.Exception.Message)"
            WordCount = 0
            MathFormulas = 0
            Examples = 0
            CodeBlocks = 0
        }
    }
}

# 扫描所有Markdown文件
$mdFiles = Get-ChildItem -Path $mathDir -Filter "*.md" -Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak)" -and
        $_.Name -notmatch "^00-"
    }

$results.TotalFiles = $mdFiles.Count

foreach ($file in $mdFiles) {
    $relativePath = $file.FullName.Replace($basePath + "\", "")
    $checkResult = Test-SubstantialContent -FilePath $file.FullName -RelativePath $relativePath

    if ($checkResult.IsSubstantial) {
        $results.SubstantialFiles++
    } else {
        $results.EmptyFiles++

        if ($checkResult.WordCount -eq 0) {
            $results.EmptyContentFiles += @{
                File = $relativePath
                Reason = $checkResult.Reason
                WordCount = 0
            }
        } else {
            $results.ShallowFiles += @{
                File = $relativePath
                Reason = $checkResult.Reason
                WordCount = $checkResult.WordCount
                MathFormulas = $checkResult.MathFormulas
                Examples = $checkResult.Examples
            }
        }
    }
}

# 生成报告
$reportFile = Join-Path $basePath "00-文档实质性内容检查报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 文档实质性内容检查报告

**检查日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**检查路径**: $mathDir

---

## 📊 统计信息

| 项目 | 数量 | 百分比 |
|------|------|--------|
| 总文档数 | $($results.TotalFiles) | 100% |
| 有实质性内容 | $($results.SubstantialFiles) | $([math]::Round($results.SubstantialFiles / $results.TotalFiles * 100, 1))% |
| 无实质性内容 | $($results.EmptyFiles) | $([math]::Round($results.EmptyFiles / $results.TotalFiles * 100, 1))% |
| 完全空文档 | $($results.EmptyContentFiles.Count) | $([math]::Round($results.EmptyContentFiles.Count / $results.TotalFiles * 100, 1))% |
| 浅层文档 | $($results.ShallowFiles.Count) | $([math]::Round($results.ShallowFiles.Count / $results.TotalFiles * 100, 1))% |

---

## 📝 完全空文档列表（$($results.EmptyContentFiles.Count)个）

"@

if ($results.EmptyContentFiles.Count -gt 0) {
    foreach ($item in ($results.EmptyContentFiles | Sort-Object File)) {
        $report += "- **$($item.File)**: $($item.Reason)`n"
    }
} else {
    $report += "未发现完全空文档。`n"
}

$report += @"

---

## 📝 浅层文档列表（字数不足500或缺少实质性内容，共$($results.ShallowFiles.Count)个）

"@

if ($results.ShallowFiles.Count -gt 0) {
    # 按字数排序
    $sortedShallow = $results.ShallowFiles | Sort-Object WordCount

    foreach ($item in $sortedShallow) {
        $report += "- **$($item.File)**`n"
        $report += "  - 字数: $($item.WordCount)`n"
        $report += "  - 数学公式: $($item.MathFormulas)`n"
        $report += "  - 例子数: $($item.Examples)`n"
        $report += "  - 问题: $($item.Reason)`n`n"
    }
} else {
    $report += "未发现浅层文档。`n"
}

$report += @"

---

## 🎯 改进建议

### 优先级分类

**P0（立即处理）**: 完全空文档（$($results.EmptyContentFiles.Count)个）
- 需要立即补充内容或标记为待完成

**P1（高优先级）**: 字数不足200的浅层文档
- 需要大幅扩充内容

**P2（中优先级）**: 字数200-500的浅层文档
- 需要补充数学公式、例子等

**P3（低优先级）**: 字数500以上但缺少数学公式的文档
- 需要补充数学内容

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$report | Out-File -FilePath $reportFile -Encoding UTF8

Write-Host "`n检查完成!" -ForegroundColor Green
Write-Host "总文档数: $($results.TotalFiles)" -ForegroundColor Cyan
Write-Host "有实质性内容: $($results.SubstantialFiles) ($([math]::Round($results.SubstantialFiles / $results.TotalFiles * 100, 1))%)" -ForegroundColor Green
Write-Host "无实质性内容: $($results.EmptyFiles) ($([math]::Round($results.EmptyFiles / $results.TotalFiles * 100, 1))%)" -ForegroundColor Yellow
Write-Host "完全空文档: $($results.EmptyContentFiles.Count)" -ForegroundColor Red
Write-Host "浅层文档: $($results.ShallowFiles.Count)" -ForegroundColor Yellow
Write-Host "报告已保存到: $reportFile" -ForegroundColor Cyan
