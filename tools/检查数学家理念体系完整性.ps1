# FormalMath项目检查数学家理念体系完整性脚本
# 创建日期: 2025年12月31日
# 用途: 全面检查数学家理念体系目录的完整性

$basePath = Split-Path -Parent $PSScriptRoot
$mathDir = Join-Path $basePath "数学家理念体系"

Write-Host "开始检查数学家理念体系完整性..." -ForegroundColor Green

# 标准目录结构
$standardSubDirs = @(
    "01-核心理论",
    "02-数学内容深度分析",
    "03-教育与影响",
    "04-历史与传记",
    "05-现代应用与拓展",
    "06-对比研究",
    "07-现代视角与评价",
    "08-知识关联分析"
)

$standardFiles = @(
    "README.md",
    "00-项目状态.md",
    "00-文档索引.md",
    "START-HERE.md"
)

$results = @{
    TotalMathematicians = 0
    Complete = 0
    Incomplete = 0
    MissingFiles = @{}
    MissingDirs = @{}
    FormatIssues = @{}
    DepthIssues = @{}
}

# 获取所有数学家目录
$mathDirs = Get-ChildItem -Path $mathDir -Directory |
    Where-Object { $_.Name -notmatch "^00-" }

$results.TotalMathematicians = $mathDirs.Count

foreach ($mathDirItem in $mathDirs) {
    $mathName = $mathDirItem.Name
    $mathPath = $mathDirItem.FullName
    $issues = @()
    $isComplete = $true

    # 检查标准文件
    foreach ($file in $standardFiles) {
        $filePath = Join-Path $mathPath $file
        if (-not (Test-Path $filePath)) {
            $issues += "缺少文件: $file"
            $isComplete = $false
            if (-not $results.MissingFiles.ContainsKey($mathName)) {
                $results.MissingFiles[$mathName] = @()
            }
            $results.MissingFiles[$mathName] += $file
        }
    }

    # 检查标准目录
    foreach ($subDir in $standardSubDirs) {
        $subDirPath = Join-Path $mathPath $subDir
        if (-not (Test-Path $subDirPath)) {
            $issues += "缺少目录: $subDir"
            $isComplete = $false
            if (-not $results.MissingDirs.ContainsKey($mathName)) {
                $results.MissingDirs[$mathName] = @()
            }
            $results.MissingDirs[$mathName] += $subDir
        }
    }

    # 检查文档格式（简单检查）
    $mdFiles = Get-ChildItem -Path $mathPath -Filter "*.md" -Recurse -File |
        Where-Object { $_.Name -notmatch "^00-" }

    foreach ($mdFile in $mdFiles | Select-Object -First 5) {
        $content = Get-Content -Path $mdFile.FullName -Raw -Encoding UTF8 -ErrorAction SilentlyContinue
        if ($content) {
            # 检查是否有文档头部元数据
            if ($content -notmatch "(创建日期|最后更新|制定日期)") {
                if (-not $results.FormatIssues.ContainsKey($mathName)) {
                    $results.FormatIssues[$mathName] = @()
                }
                $results.FormatIssues[$mathName] += $mdFile.Name
            }

            # 检查内容深度（字数）
            $wordCount = ([regex]::Matches($content, "[\u4e00-\u9fa5]")).Count + ([regex]::Matches($content, "\b[a-zA-Z]+\b")).Count
            if ($wordCount -lt 1000) {
                if (-not $results.DepthIssues.ContainsKey($mathName)) {
                    $results.DepthIssues[$mathName] = @()
                }
                $results.DepthIssues[$mathName] += "$($mdFile.Name): $wordCount 字"
            }
        }
    }

    if ($isComplete) {
        $results.Complete++
    } else {
        $results.Incomplete++
    }
}

# 生成报告
$reportFile = Join-Path $basePath "00-数学家理念体系完整性检查报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 数学家理念体系完整性检查报告

**检查日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**检查路径**: $mathDir

---

## 📊 统计信息

| 项目 | 数量 |
|------|------|
| 总数学家数 | $($results.TotalMathematicians) |
| 完整目录 | $($results.Complete) |
| 不完整目录 | $($results.Incomplete) |
| 缺少文件 | $($results.MissingFiles.Count) 个目录 |
| 缺少目录 | $($results.MissingDirs.Count) 个目录 |
| 格式问题 | $($results.FormatIssues.Count) 个目录 |
| 深度问题 | $($results.DepthIssues.Count) 个目录 |

---

## 📝 缺少文件列表

"@

if ($results.MissingFiles.Count -gt 0) {
    foreach ($mathName in ($results.MissingFiles.Keys | Sort-Object)) {
        $report += "### $mathName`n`n"
        foreach ($file in $results.MissingFiles[$mathName]) {
            $report += "- [ ] 缺少: $file`n"
        }
        $report += "`n"
    }
} else {
    $report += "所有目录都包含必需文件。`n`n"
}

$report += @"

## 📝 缺少目录列表

"@

if ($results.MissingDirs.Count -gt 0) {
    foreach ($mathName in ($results.MissingDirs.Keys | Sort-Object)) {
        $report += "### $mathName`n`n"
        foreach ($dir in $results.MissingDirs[$mathName]) {
            $report += "- [ ] 缺少: $dir`n"
        }
        $report += "`n"
    }
} else {
    $report += "所有目录都包含必需子目录。`n`n"
}

$report += @"

## 📝 格式问题列表

"@

if ($results.FormatIssues.Count -gt 0) {
    foreach ($mathName in ($results.FormatIssues.Keys | Sort-Object)) {
        $report += "### $mathName`n`n"
        foreach ($file in ($results.FormatIssues[$mathName] | Select-Object -First 5)) {
            $report += "- 格式问题: $file`n"
        }
        $report += "`n"
    }
} else {
    $report += "未发现格式问题。`n`n"
}

$report += @"

## 📝 深度问题列表（浅层内容）

"@

if ($results.DepthIssues.Count -gt 0) {
    foreach ($mathName in ($results.DepthIssues.Keys | Sort-Object)) {
        $report += "### $mathName`n`n"
        foreach ($issue in ($results.DepthIssues[$mathName] | Select-Object -First 5)) {
            $report += "- 深度问题: $issue`n"
        }
        $report += "`n"
    }
} else {
    $report += "未发现深度问题。`n`n"
}

$report += @"

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$report | Out-File -FilePath $reportFile -Encoding UTF8
Write-Host "`n检查完成!" -ForegroundColor Green
Write-Host "总数学家数: $($results.TotalMathematicians)" -ForegroundColor Cyan
Write-Host "完整目录: $($results.Complete)" -ForegroundColor Green
Write-Host "不完整目录: $($results.Incomplete)" -ForegroundColor Yellow
Write-Host "报告已保存到: $reportFile" -ForegroundColor Cyan
