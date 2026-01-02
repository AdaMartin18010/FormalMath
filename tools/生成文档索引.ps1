# FormalMath项目生成文档索引脚本
# 创建日期: 2025年12月31日
# 用途: 生成全局文档索引

$basePath = Split-Path -Parent $PSScriptRoot

Write-Host "开始生成文档索引..." -ForegroundColor Green

# 定义目录分类
$categories = @{
    "01-基础数学" = "基础数学"
    "02-代数结构" = "代数结构"
    "03-分析学" = "分析学"
    "04-几何学" = "几何学"
    "05-拓扑学" = "拓扑学"
    "06-数论" = "数论"
    "07-逻辑学" = "逻辑学"
    "08-计算数学" = "计算数学"
    "09-形式化证明" = "形式化证明"
    "10-语义模型" = "语义模型"
    "11-高级数学" = "高级数学"
    "12-应用数学" = "应用数学"
    "13-代数几何" = "代数几何"
    "14-微分几何" = "微分几何"
    "15-同调代数" = "同调代数"
    "00-核心概念理解三问" = "核心概念理解"
}

$docsPath = Join-Path $basePath "docs"
$index = @{
    Categories = @{}
    Total = 0
}

# 扫描各分类目录
foreach ($category in $categories.Keys) {
    $categoryPath = Join-Path $docsPath $category
    if (-not (Test-Path $categoryPath)) {
        continue
    }

    $files = Get-ChildItem -Path $categoryPath -Filter "*.md" -Recurse -File |
        Where-Object {
            $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak)" -and
            $_.Name -notmatch "^00-README"
        }

    $categoryFiles = @()
    foreach ($file in $files) {
        $relativePath = $file.FullName.Replace($basePath, "").TrimStart('\')
        $relativePath = $relativePath.Replace('\', '/')

        # 获取文档标题
        $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8 -ErrorAction SilentlyContinue
        $titleMatch = [regex]::Match($content, "^#\s+(.+)$", [System.Text.RegularExpressions.RegexOptions]::Multiline)
        $title = if ($titleMatch.Success) { $titleMatch.Groups[1].Value.Trim() } else { $file.BaseName }

        $categoryFiles += [PSCustomObject]@{
            Title = $title
            Path = $relativePath
            Name = $file.Name
        }
        $index.Total++
    }

    $index.Categories[$categories[$category]] = $categoryFiles
}

# 生成索引文档
$indexFile = Join-Path $basePath "docs\00-全局文档索引-2025年12月.md"
$indexContent = @"
# FormalMath项目全局文档索引

**创建日期**: 2025年12月31日
**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
**总文档数**: $($index.Total)

---

## 📋 索引概述

本文档提供FormalMath项目的完整文档索引，按数学分支分类组织。

---

## 📚 文档分类索引

"@

foreach ($categoryName in ($index.Categories.Keys | Sort-Object)) {
    $files = $index.Categories[$categoryName]
    if ($files.Count -eq 0) {
        continue
    }

    $indexContent += "`n### $categoryName`n`n"
    $indexContent += "**文档数**: $($files.Count) 个`n`n"

    foreach ($file in $files | Sort-Object Title) {
        $indexContent += "- [$($file.Title)]($($file.Path))`n"
    }
}

$indexContent += @"

---

## 📊 统计信息

| 分类 | 文档数 |
|------|--------|
"@

foreach ($categoryName in ($index.Categories.Keys | Sort-Object)) {
    $count = $index.Categories[$categoryName].Count
    if ($count -gt 0) {
        $indexContent += "| $categoryName | $count |`n"
    }
}

$indexContent += "| **总计** | **$($index.Total)** |`n"

$indexContent += @"

---

## 🔍 快速查找

### 按数学分支查找

- [基础数学](#基础数学)
- [代数结构](#代数结构)
- [分析学](#分析学)
- [几何学](#几何学)
- [拓扑学](#拓扑学)
- [数论](#数论)
- [逻辑学](#逻辑学)
- [计算数学](#计算数学)
- [形式化证明](#形式化证明)
- [语义模型](#语义模型)
- [高级数学](#高级数学)
- [应用数学](#应用数学)
- [代数几何](#代数几何)
- [微分几何](#微分几何)
- [同调代数](#同调代数)
- [核心概念理解](#核心概念理解)

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$indexContent | Out-File -FilePath $indexFile -Encoding UTF8
Write-Host "✓ 文档索引已生成: $indexFile" -ForegroundColor Green
Write-Host "  总文档数: $($index.Total)" -ForegroundColor Cyan
