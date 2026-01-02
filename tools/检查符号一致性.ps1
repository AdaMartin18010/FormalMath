# FormalMath项目检查符号一致性脚本
# 创建日期: 2025年12月31日
# 用途: 检查文档中符号使用的一致性

$basePath = Split-Path -Parent $PSScriptRoot
$docsPath = Join-Path $basePath "docs"

Write-Host "开始检查符号一致性..." -ForegroundColor Green

# 读取符号规范，建立标准符号列表
$symbolFile = Join-Path $docsPath "FormalMath符号使用规范.md"
$standardSymbols = @{}

if (Test-Path $symbolFile) {
    $content = Get-Content -Path $symbolFile -Raw -Encoding UTF8
    # 提取符号定义（从表格中）
    $symbolPattern = '\|\s*\$([^\$]+)\$\s*\|\s*`([^`]+)`\s*\|'
    $matches = [regex]::Matches($content, $symbolPattern)

    foreach ($match in $matches) {
        $symbol = $match.Groups[1].Value.Trim()
        $latexCode = $match.Groups[2].Value.Trim()
        if (-not $standardSymbols.ContainsKey($symbol)) {
            $standardSymbols[$symbol] = $latexCode
        }
    }
}

Write-Host "已加载 $($standardSymbols.Count) 个标准符号" -ForegroundColor Cyan

# 扫描文档，检查符号使用
$files = Get-ChildItem -Path $docsPath -Filter "*.md" -Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak|符号使用规范|索引|导航)" -and
        $_.Name -notmatch "^00-"
    } | Select-Object -First 100  # 限制处理数量以避免超时

$inconsistencies = @()
$processed = 0

foreach ($file in $files) {
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8 -ErrorAction SilentlyContinue
    if (-not $content) { continue }

    $relativePath = $file.FullName.Replace($basePath, "").TrimStart('\').Replace('\', '/')

    # 检查LaTeX符号使用
    $latexPattern = '\$([^\$]+)\$'
    $latexMatches = [regex]::Matches($content, $latexPattern)

    foreach ($latexMatch in $latexMatches) {
        $latexCode = $latexMatch.Groups[1].Value.Trim()
        # 检查是否使用了标准符号
        foreach ($symbol in $standardSymbols.Keys) {
            $standardCode = $standardSymbols[$symbol]
            # 如果LaTeX代码包含符号但不匹配标准代码
            if ($latexCode -match [regex]::Escape($symbol) -and $latexCode -ne $standardCode) {
                $inconsistencies += [PSCustomObject]@{
                    File = $relativePath
                    Symbol = $symbol
                    StandardCode = $standardCode
                    FoundCode = $latexCode
                    Issue = "符号代码不一致"
                }
            }
        }
    }

    $processed++
    if ($processed % 10 -eq 0) {
        Write-Host "已处理: $processed 个文档..." -ForegroundColor Cyan
    }
}

# 生成报告
$reportFile = Join-Path $basePath "00-符号一致性检查报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 符号一致性检查报告

**检查日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**标准符号数**: $($standardSymbols.Count)
**检查文档数**: $processed
**不一致项**: $($inconsistencies.Count)

---

## 📊 统计信息

| 项目 | 数量 |
|------|------|
| 标准符号数 | $($standardSymbols.Count) |
| 检查文档数 | $processed |
| 不一致项 | $($inconsistencies.Count) |

---

## 📝 不一致项列表（前50个）

"@

if ($inconsistencies.Count -gt 0) {
    foreach ($issue in $inconsistencies | Select-Object -First 50) {
        $report += "### $($issue.File)`n`n"
        $report += "- **符号**: $($issue.Symbol)`n"
        $report += "- **标准代码**: ``$($issue.StandardCode)```n"
        $report += "- **发现代码**: ``$($issue.FoundCode)```n"
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
Write-Host "标准符号数: $($standardSymbols.Count)" -ForegroundColor Cyan
Write-Host "检查文档数: $processed" -ForegroundColor Cyan
Write-Host "不一致项: $($inconsistencies.Count)" -ForegroundColor $(if ($inconsistencies.Count -eq 0) { "Green" } else { "Yellow" })
Write-Host "报告已保存到: $reportFile" -ForegroundColor Cyan
