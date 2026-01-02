# FormalMath项目建立关联链接脚本
# 创建日期: 2025年12月31日
# 用途: 识别并建立文档间的关联链接

$basePath = Split-Path -Parent $PSScriptRoot
$docsPath = Join-Path $basePath "docs"

Write-Host "开始建立关联链接..." -ForegroundColor Green

# 读取术语词典，建立术语到文档的映射
$termToDocs = @{}
$termFiles = Get-ChildItem -Path $docsPath -Filter "*术语词典*.md" -File

foreach ($termFile in $termFiles) {
    $content = Get-Content -Path $termFile.FullName -Raw -Encoding UTF8
    # 提取术语
    $terms = [regex]::Matches($content, "###\s+(.+?)(?:\n|$)", [System.Text.RegularExpressions.RegexOptions]::Multiline)
    foreach ($term in $terms) {
        $termName = $term.Groups[1].Value.Trim()
        $relativePath = $termFile.FullName.Replace($basePath, "").TrimStart('\').Replace('\', '/')
        if (-not $termToDocs.ContainsKey($termName)) {
            $termToDocs[$termName] = @()
        }
        $termToDocs[$termName] += $relativePath
    }
}

# 扫描所有文档，识别关联
$files = Get-ChildItem -Path $docsPath -Filter "*.md" -Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak|README|索引|导航)" -and
        $_.Name -notmatch "^00-"
    }

$associations = @()
$processed = 0

foreach ($file in $files) {
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8 -ErrorAction SilentlyContinue
    if (-not $content) { continue }

    $relativePath = $file.FullName.Replace($basePath, "").TrimStart('\').Replace('\', '/')

    # 查找术语引用
    foreach ($term in $termToDocs.Keys) {
        if ($content -match [regex]::Escape($term)) {
            foreach ($docPath in $termToDocs[$term]) {
                if ($docPath -ne $relativePath) {
                    $associations += [PSCustomObject]@{
                        Source = $relativePath
                        Target = $docPath
                        Type = "术语关联"
                        Term = $term
                    }
                }
            }
        }
    }

    $processed++
    if ($processed % 50 -eq 0) {
        Write-Host "已处理: $processed 个文档..." -ForegroundColor Cyan
    }
}

# 生成关联报告
$reportFile = Join-Path $basePath "docs\00-文档关联报告-2025年12月.md"
$report = @"
# FormalMath项目文档关联报告

**生成日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**总关联数**: $($associations.Count)

---

## 📋 关联概述

本文档记录FormalMath项目中文档间的关联关系，帮助建立双向链接。

---

## 🔗 关联统计

| 类型 | 数量 |
|------|------|
| 术语关联 | $($associations.Count) |

---

## 📝 关联列表（前100个）

"@

$uniqueAssociations = $associations | Group-Object @{Expression={$_.Source + " -> " + $_.Target}} | Select-Object -First 100

foreach ($assoc in $uniqueAssociations) {
    $first = $assoc.Group[0]
    $report += "### $($first.Source)`n`n"
    $report += "- **关联到**: [$($first.Target)]($($first.Target))`n"
    $report += "- **关联类型**: $($first.Type)`n"
    if ($first.Term) {
        $report += "- **关联术语**: $($first.Term)`n"
    }
    $report += "`n"
}

if ($associations.Count -gt 100) {
    $report += "`n... 还有 $($associations.Count - 100) 个关联`n"
}

$report += @"

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$report | Out-File -FilePath $reportFile -Encoding UTF8
Write-Host "✓ 关联报告已生成: $reportFile" -ForegroundColor Green
Write-Host "  总关联数: $($associations.Count)" -ForegroundColor Cyan
