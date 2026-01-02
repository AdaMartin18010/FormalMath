# FormalMath项目生成概念索引脚本
# 创建日期: 2025年12月31日
# 用途: 生成概念索引

$basePath = Split-Path -Parent $PSScriptRoot

Write-Host "开始生成概念索引..." -ForegroundColor Green

# 读取术语词典总索引
$termIndexPath = Join-Path $basePath "docs\FormalMath术语词典总索引.md"
$concepts = @()

if (Test-Path $termIndexPath) {
    $termIndexContent = Get-Content -Path $termIndexPath -Raw -Encoding UTF8
    # 提取术语词典链接
    $termLinks = [regex]::Matches($termIndexContent, "\[([^\]]+)\]\(([^\)]+)\)")

    foreach ($match in $termLinks) {
        $termName = $match.Groups[1].Value
        $termPath = $match.Groups[2].Value

        # 检查是否是术语词典文件
        if ($termPath -match "术语词典") {
            $concepts += [PSCustomObject]@{
                Name = $termName
                Path = $termPath
                Category = "术语词典"
            }
        }
    }
}

# 扫描docs目录，查找定义
$docsPath = Join-Path $basePath "docs"
$files = Get-ChildItem -Path $docsPath -Filter "*.md" -Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak|README)" -and
        $_.Name -notmatch "^00-"
    }

$definitionPattern = "定义\s+\d+\.\d+|Definition\s+\d+\.\d+"
$conceptPattern = "##\s+(.+?)(?:\n|$)"

foreach ($file in $files) {
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8 -ErrorAction SilentlyContinue
    if (-not $content) { continue }

    $relativePath = $file.FullName.Replace($basePath, "").TrimStart('\').Replace('\', '/')

    # 提取定义
    $definitions = [regex]::Matches($content, $definitionPattern)
    foreach ($def in $definitions) {
        # 尝试提取定义名称
        $context = $content.Substring([Math]::Max(0, $def.Index - 100), [Math]::Min(200, $content.Length - $def.Index + 100))
        $nameMatch = [regex]::Match($context, "([A-Za-z\u4e00-\u9fa5]+)\s*(?:定义|Definition)", [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)
        if ($nameMatch.Success) {
            $conceptName = $nameMatch.Groups[1].Value.Trim()
            if ($conceptName.Length -gt 1 -and $conceptName.Length -lt 50) {
                $concepts += [PSCustomObject]@{
                    Name = $conceptName
                    Path = $relativePath
                    Category = "定义"
                }
            }
        }
    }

    # 提取二级标题作为概念
    $headings = [regex]::Matches($content, "##\s+(.+?)(?:\n|$)", [System.Text.RegularExpressions.RegexOptions]::Multiline)
    foreach ($heading in $headings) {
        $headingText = $heading.Groups[1].Value.Trim()
        # 过滤掉一些非概念标题
        if ($headingText -notmatch "^(目录|概述|参考文献|相关链接|附录|总结|概述|Overview|References|Related)" -and
            $headingText.Length -gt 2 -and $headingText.Length -lt 100) {
            $concepts += [PSCustomObject]@{
                Name = $headingText
                Path = $relativePath
                Category = "章节"
            }
        }
    }
}

# 去重并分类
$uniqueConcepts = $concepts | Group-Object Name | ForEach-Object {
    $first = $_.Group[0]
    [PSCustomObject]@{
        Name = $first.Name
        Paths = ($_.Group | Select-Object -ExpandProperty Path -Unique)
        Categories = ($_.Group | Select-Object -ExpandProperty Category -Unique)
    }
}

# 按分类组织
$conceptsByCategory = @{}
foreach ($concept in $uniqueConcepts) {
    foreach ($category in $concept.Categories) {
        if (-not $conceptsByCategory.ContainsKey($category)) {
            $conceptsByCategory[$category] = @()
        }
        $conceptsByCategory[$category] += $concept
    }
}

# 生成索引文档
$indexFile = Join-Path $basePath "docs\00-概念索引-2025年12月.md"
$indexContent = @"
# FormalMath项目概念索引

**创建日期**: 2025年12月31日
**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
**总概念数**: $($uniqueConcepts.Count)

---

## 📋 索引概述

本文档提供FormalMath项目的概念索引，包括术语词典、定义和主要章节。

---

## 📚 概念分类索引

"@

foreach ($category in ($conceptsByCategory.Keys | Sort-Object)) {
    $categoryConcepts = $conceptsByCategory[$category]
    $indexContent += "`n### $category`n`n"
    $indexContent += "**概念数**: $($categoryConcepts.Count) 个`n`n"

    foreach ($concept in ($categoryConcepts | Sort-Object Name)) {
        if ($concept.Paths.Count -eq 1) {
            $indexContent += "- **$($concept.Name)**: [$($concept.Paths[0])]($($concept.Paths[0]))`n"
        } else {
            $indexContent += "- **$($concept.Name)**: "
            $links = @()
            foreach ($path in $concept.Paths) {
                $fileName = Split-Path -Leaf $path
                $links += "[$fileName]($path)"
            }
            $indexContent += ($links -join ", ") + "`n"
        }
    }
}

$indexContent += @"

---

## 📊 统计信息

| 分类 | 概念数 |
|------|--------|
"@

foreach ($category in ($conceptsByCategory.Keys | Sort-Object)) {
    $count = $conceptsByCategory[$category].Count
    $indexContent += "| $category | $count |`n"
}

$indexContent += "| **总计** | **$($uniqueConcepts.Count)** |`n"

$indexContent += @"

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$indexContent | Out-File -FilePath $indexFile -Encoding UTF8
Write-Host "✓ 概念索引已生成: $indexFile" -ForegroundColor Green
Write-Host "  总概念数: $($uniqueConcepts.Count)" -ForegroundColor Cyan
