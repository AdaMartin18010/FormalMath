# FormalMath项目批量删除模板文档脚本
# 创建日期: 2025年12月31日
# 用途: 批量删除无用的模板文档

param(
    [switch]$DryRun,
    [switch]$Backup
)

$basePath = Split-Path -Parent $PSScriptRoot
$mathDir = Join-Path $basePath "数学家理念体系"

Write-Host "开始扫描模板文档..." -ForegroundColor Green

# 模板文字模式
$templatePatterns = @(
    '该应用的核心要点和意义',
    '在数学和科学的多个领域都有重要应用',
    '从理论物理到工程实践，这一理论都发挥着重要作用',
    '体现了.*对数学的深刻洞察和创新思维',
    '这一理论在数学史上占有重要地位',
    '待补充|TODO|待完善|待完成|待添加|placeholder|template|模板|占位符'
)

$results = @{
    TotalFiles = 0
    TemplateFiles = @()
    EmptyFiles = @()
    DeletedFiles = @()
}

# 检查是否为模板文档
function Test-TemplateDocument {
    param(
        [string]$FilePath
    )

    try {
        $content = Get-Content -Path $FilePath -Raw -Encoding UTF8 -ErrorAction Stop

        if ([string]::IsNullOrWhiteSpace($content)) {
            return @{
                IsTemplate = $true
                Reason = "文件为空"
                Type = "Empty"
            }
        }

        # 计算字数
        $chineseChars = ([regex]::Matches($content, "[\u4e00-\u9fa5]")).Count
        $englishWords = ([regex]::Matches($content, "\b[a-zA-Z]{2,}\b")).Count
        $wordCount = $chineseChars + $englishWords

        # 检查字数
        if ($wordCount -lt 100) {
            return @{
                IsTemplate = $true
                Reason = "字数过少($wordCount < 100)"
                Type = "Shallow"
            }
        }

        # 检查模板文字
        $templateCount = 0
        foreach ($pattern in $templatePatterns) {
            if ($content -match $pattern) {
                $templateCount++
            }
        }

        # 如果包含3个或更多模板模式，认为是模板文档
        if ($templateCount -ge 3) {
            return @{
                IsTemplate = $true
                Reason = "包含$templateCount个模板模式"
                Type = "Template"
            }
        }

        # 检查是否只有标题和目录
        $lines = $content -split "`n" | Where-Object {
            $_.Trim() -ne "" -and
            $_ -notmatch '^#{1,6}\s' -and
            $_ -notmatch '^-\s*\[.*\]\(.*\)' -and
            $_ -notmatch '^\s*\|.*\|'
        }

        if ($lines.Count -lt 5 -and $wordCount -lt 300) {
            return @{
                IsTemplate = $true
                Reason = "只有标题和目录结构"
                Type = "StructureOnly"
            }
        }

        return @{
            IsTemplate = $false
            Reason = "通过"
            Type = "Valid"
        }
    }
    catch {
        return @{
            IsTemplate = $false
            Reason = "读取错误: $($_.Exception.Message)"
            Type = "Error"
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
    $checkResult = Test-TemplateDocument -FilePath $file.FullName

    if ($checkResult.IsTemplate) {
        if ($checkResult.Type -eq "Empty") {
            $results.EmptyFiles += @{
                File = $relativePath
                Reason = $checkResult.Reason
            }
        } else {
            $results.TemplateFiles += @{
                File = $relativePath
                Reason = $checkResult.Reason
                Type = $checkResult.Type
            }
        }
    }
}

# 生成报告
$reportFile = Join-Path $basePath "00-模板文档删除报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 模板文档删除报告

**扫描日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**扫描路径**: $mathDir

---

## 📊 统计信息

| 项目 | 数量 |
|------|------|
| 总文档数 | $($results.TotalFiles) |
| 模板文档 | $($results.TemplateFiles.Count) |
| 完全空文档 | $($results.EmptyFiles.Count) |
| **建议删除** | $($results.TemplateFiles.Count + $results.EmptyFiles.Count) |

---

## 📝 完全空文档列表（$($results.EmptyFiles.Count)个）

"@

if ($results.EmptyFiles.Count -gt 0) {
    foreach ($item in ($results.EmptyFiles | Sort-Object File)) {
        $report += "- **$($item.File)**: $($item.Reason)`n"
    }
} else {
    $report += "未发现完全空文档。`n"
}

$report += @"

---

## 📝 模板文档列表（$($results.TemplateFiles.Count)个）

"@

if ($results.TemplateFiles.Count -gt 0) {
    foreach ($item in ($results.TemplateFiles | Sort-Object File)) {
        $report += "- **$($item.File)**`n"
        $report += "  - 类型: $($item.Type)`n"
        $report += "  - 原因: $($item.Reason)`n`n"
    }
} else {
    $report += "未发现模板文档。`n"
}

$report += @"

---

## 🎯 删除建议

### 建议删除的文档

以下文档建议删除（共$($results.TemplateFiles.Count + $results.EmptyFiles.Count)个）：

1. **完全空文档** ($($results.EmptyFiles.Count)个): 立即删除
2. **模板文档** ($($results.TemplateFiles.Count)个): 审查后删除

### 删除前检查

删除前请确认：
- [ ] 文档确实没有实质性内容
- [ ] 文档不在索引或导航中引用
- [ ] 删除不会影响其他文档

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$report | Out-File -FilePath $reportFile -Encoding UTF8

Write-Host "`n扫描完成!" -ForegroundColor Green
Write-Host "总文档数: $($results.TotalFiles)" -ForegroundColor Cyan
Write-Host "模板文档: $($results.TemplateFiles.Count)" -ForegroundColor Yellow
Write-Host "完全空文档: $($results.EmptyFiles.Count)" -ForegroundColor Red
Write-Host "建议删除: $($results.TemplateFiles.Count + $results.EmptyFiles.Count)" -ForegroundColor Yellow
Write-Host "报告已保存到: $reportFile" -ForegroundColor Cyan

if ($DryRun) {
    Write-Host "`n这是试运行模式，未实际删除文件。" -ForegroundColor Yellow
} else {
    Write-Host "`n⚠️  警告: 未启用DryRun模式，但脚本不会自动删除文件。" -ForegroundColor Yellow
    Write-Host "请手动审查报告后决定是否删除。" -ForegroundColor Yellow
}
