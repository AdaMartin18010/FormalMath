# FormalMath项目检查术语一致性脚本
# 创建日期: 2025年12月31日
# 用途: 检查文档中术语使用的一致性

$basePath = Split-Path -Parent $PSScriptRoot
$docsPath = Join-Path $basePath "docs"

Write-Host "开始检查术语一致性..." -ForegroundColor Green

# 读取术语词典，建立标准术语列表
$standardTerms = @{}
$termFiles = Get-ChildItem -Path $docsPath -Filter "*术语词典*.md" -File

foreach ($termFile in $termFiles) {
    $content = Get-Content -Path $termFile.FullName -Raw -Encoding UTF8
    # 提取术语定义
    $terms = [regex]::Matches($content, "###\s+(.+?)(?:\n|$)", [System.Text.RegularExpressions.RegexOptions]::Multiline)
    foreach ($term in $terms) {
        $termName = $term.Groups[1].Value.Trim()
        # 提取中英文术语
        if ($termName -match "(.+?)\s*/\s*(.+)") {
            $chinese = $matches[1].Trim()
            $english = $matches[2].Trim()
            if (-not $standardTerms.ContainsKey($chinese)) {
                $standardTerms[$chinese] = @{
                    English = $english
                    Source = $termFile.Name
                }
            }
        } else {
            if (-not $standardTerms.ContainsKey($termName)) {
                $standardTerms[$termName] = @{
                    English = ""
                    Source = $termFile.Name
                }
            }
        }
    }
}

Write-Host "已加载 $($standardTerms.Count) 个标准术语" -ForegroundColor Cyan

# 扫描文档，检查术语使用
$files = Get-ChildItem -Path $docsPath -Filter "*.md" -Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak|术语词典|索引|导航)" -and
        $_.Name -notmatch "^00-"
    }

$inconsistencies = @()
$processed = 0

foreach ($file in $files) {
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8 -ErrorAction SilentlyContinue
    if (-not $content) { continue }

    $relativePath = $file.FullName.Replace($basePath, "").TrimStart('\').Replace('\', '/')

    # 检查每个标准术语的使用
    foreach ($term in $standardTerms.Keys) {
        # 查找术语使用
        $matches = [regex]::Matches($content, [regex]::Escape($term))
        if ($matches.Count -gt 0) {
            # 检查是否有不一致的使用（例如使用了不同的英文翻译）
            $englishTerm = $standardTerms[$term].English
            if ($englishTerm -and $content -notmatch $englishTerm) {
                # 查找可能的其他英文翻译
                $otherEnglish = [regex]::Matches($content, "\b[A-Z][a-z]+(?:\s+[A-Z][a-z]+)*\b")
                foreach ($other in $otherEnglish) {
                    if ($other.Value -ne $englishTerm -and $other.Value.Length -gt 3) {
                        $inconsistencies += [PSCustomObject]@{
                            File = $relativePath
                            Term = $term
                            StandardEnglish = $englishTerm
                            FoundEnglish = $other.Value
                            Issue = "英文术语不一致"
                        }
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

# 生成报告
$reportFile = Join-Path $basePath "00-术语一致性检查报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 术语一致性检查报告

**检查日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**标准术语数**: $($standardTerms.Count)
**检查文档数**: $processed
**不一致项**: $($inconsistencies.Count)

---

## 📊 统计信息

| 项目 | 数量 |
|------|------|
| 标准术语数 | $($standardTerms.Count) |
| 检查文档数 | $processed |
| 不一致项 | $($inconsistencies.Count) |

---

## 📝 不一致项列表（前50个）

"@

if ($inconsistencies.Count -gt 0) {
    foreach ($issue in $inconsistencies | Select-Object -First 50) {
        $report += "### $($issue.File)`n`n"
        $report += "- **术语**: $($issue.Term)`n"
        $report += "- **标准英文**: $($issue.StandardEnglish)`n"
        $report += "- **发现英文**: $($issue.FoundEnglish)`n"
        $report += "- **问题**: $($issue.Issue)`n`n"
    }
    if ($inconsistencies.Count -gt 50) {
        $report += "`n... 还有 $($inconsistencies.Count - 50) 个不一致项`n"
    }
} else {
    $report += "未发现不一致项。`n`n"
}

$report += @"

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$report | Out-File -FilePath $reportFile -Encoding UTF8
Write-Host "`n检查完成!" -ForegroundColor Green
Write-Host "标准术语数: $($standardTerms.Count)" -ForegroundColor Cyan
Write-Host "检查文档数: $processed" -ForegroundColor Cyan
Write-Host "不一致项: $($inconsistencies.Count)" -ForegroundColor $(if ($inconsistencies.Count -eq 0) { "Green" } else { "Yellow" })
Write-Host "报告已保存到: $reportFile" -ForegroundColor Cyan
