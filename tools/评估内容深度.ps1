# FormalMath项目内容深度评估脚本
# 创建日期: 2025年12月31日
# 用途: 评估文档内容深度，识别浅层内容

param(
    [string]$Path = "docs",
    [switch]$Recurse
)

$basePath = Split-Path -Parent $PSScriptRoot
$checkPath = if ($Path -eq "docs") { Join-Path $basePath "docs" } else { Join-Path $basePath $Path }

Write-Host "开始评估内容深度..." -ForegroundColor Green
Write-Host "检查路径: $checkPath" -ForegroundColor Cyan

$stats = @{
    Total = 0
    L0 = 0
    L1 = 0
    L2 = 0
    L3 = 0
    Shallow = @()
    Deep = @()
}

# 深度层级定义
$depthLevels = @{
    L0 = @{ Min = 0; Max = 2000; Name = "基础层" }
    L1 = @{ Min = 2000; Max = 4000; Name = "中级层" }
    L2 = @{ Min = 4000; Max = 6000; Name = "高级层" }
    L3 = @{ Min = 6000; Max = [int]::MaxValue; Name = "研究层" }
}

function Test-ContentDepth {
    param([System.IO.FileInfo]$File)

    $stats.Total++
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8

    # 计算字数（中文字符数 + 英文单词数）
    $chineseChars = ([regex]::Matches($content, "[\u4e00-\u9fa5]")).Count
    $englishWords = ([regex]::Matches($content, "\b[a-zA-Z]+\b")).Count
    $wordCount = $chineseChars + $englishWords

    # 确定深度层级
    $level = "L0"
    if ($wordCount -ge 6000) {
        $level = "L3"
        $stats.L3++
    } elseif ($wordCount -ge 4000) {
        $level = "L2"
        $stats.L2++
    } elseif ($wordCount -ge 2000) {
        $level = "L1"
        $stats.L1++
    } else {
        $level = "L0"
        $stats.L0++
    }

    # 检查内容结构
    $hasDefinition = $content -match "(定义|Definition|定义\s+\d+\.\d+)"
    $hasTheorem = $content -match "(定理|Theorem|定理\s+\d+\.\d+)"
    $hasProof = $content -match "(证明|Proof|证明\s+\d+\.\d+)"
    $hasExample = $content -match "(例子|Example|例子\s+\d+\.\d+)"
    $hasApplication = $content -match "(应用|Application|应用\s+\d+\.\d+)"

    $structureScore = 0
    if ($hasDefinition) { $structureScore++ }
    if ($hasTheorem) { $structureScore++ }
    if ($hasProof) { $structureScore++ }
    if ($hasExample) { $structureScore++ }
    if ($hasApplication) { $structureScore++ }

    # 判断是否为浅层内容
    $isShallow = $false
    if ($level -eq "L0" -and $wordCount -lt 1000) {
        $isShallow = $true
    } elseif ($level -eq "L1" -and ($wordCount -lt 2000 -or $structureScore -lt 3)) {
        $isShallow = $true
    } elseif ($level -eq "L2" -and ($wordCount -lt 4000 -or $structureScore -lt 4)) {
        $isShallow = $true
    }

    $relativePath = $file.FullName.Replace($basePath, "").TrimStart('\')

    $result = [PSCustomObject]@{
        File = $relativePath
        WordCount = $wordCount
        Level = $level
        StructureScore = $structureScore
        HasDefinition = $hasDefinition
        HasTheorem = $hasTheorem
        HasProof = $hasProof
        HasExample = $hasExample
        HasApplication = $hasApplication
        IsShallow = $isShallow
    }

    if ($isShallow) {
        $stats.Shallow += $result
    } else {
        $stats.Deep += $result
    }

    return $result
}

# 获取文件列表
$files = Get-ChildItem -Path $checkPath -Filter "*.md" -Recurse:$Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak|README)" -and
        $_.Name -notmatch "^00-"
    }

$results = @()
foreach ($file in $files) {
    $result = Test-ContentDepth -File $file
    $results += $result
}

# 输出统计信息
Write-Host "`n评估完成!" -ForegroundColor Green
Write-Host "总文档数: $($stats.Total)" -ForegroundColor Cyan
Write-Host "`n按深度层级统计:" -ForegroundColor Yellow
Write-Host "  L0 (基础层): $($stats.L0)" -ForegroundColor Cyan
Write-Host "  L1 (中级层): $($stats.L1)" -ForegroundColor Green
Write-Host "  L2 (高级层): $($stats.L2)" -ForegroundColor Yellow
Write-Host "  L3 (研究层): $($stats.L3)" -ForegroundColor Magenta
Write-Host "`n浅层内容: $($stats.Shallow.Count)" -ForegroundColor Red
Write-Host "深层内容: $($stats.Deep.Count)" -ForegroundColor Green

# 生成报告文件
$reportFile = Join-Path $basePath "00-内容深度评估报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 内容深度评估报告

**评估日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**评估路径**: $checkPath

## 📊 统计信息

| 项目 | 数量 |
|------|------|
| 总文档数 | $($stats.Total) |
| L0 (基础层) | $($stats.L0) |
| L1 (中级层) | $($stats.L1) |
| L2 (高级层) | $($stats.L2) |
| L3 (研究层) | $($stats.L3) |
| 浅层内容 | $($stats.Shallow.Count) |
| 深层内容 | $($stats.Deep.Count) |

## 📋 浅层内容列表（需要改进）

"@

if ($stats.Shallow.Count -gt 0) {
    foreach ($doc in $stats.Shallow | Sort-Object WordCount) {
        $report += "### $($doc.File)`n`n"
        $report += "- **字数**: $($doc.WordCount) 字`n"
        $report += "- **层级**: $($doc.Level)`n"
        $report += "- **结构得分**: $($doc.StructureScore)/5`n"
        $report += "- **问题**: "
        $issues = @()
        if (-not $doc.HasDefinition) { $issues += "缺少定义" }
        if (-not $doc.HasTheorem) { $issues += "缺少定理" }
        if (-not $doc.HasProof) { $issues += "缺少证明" }
        if (-not $doc.HasExample) { $issues += "缺少例子" }
        if (-not $doc.HasApplication) { $issues += "缺少应用" }
        if ($issues.Count -gt 0) {
            $report += $issues -join ", "
        } else {
            $report += "字数不足"
        }
        $report += "`n`n"
    }
} else {
    $report += "暂无浅层内容。`n`n"
}

$report += @"

## 📋 深层内容列表（优秀）

"@

if ($stats.Deep.Count -gt 0) {
    foreach ($doc in $stats.Deep | Sort-Object WordCount -Descending | Select-Object -First 20) {
        $report += "- **$($doc.File)**: $($doc.WordCount) 字 ($($doc.Level))`n"
    }
    if ($stats.Deep.Count -gt 20) {
        $report += "`n... 还有 $($stats.Deep.Count - 20) 个深层文档`n"
    }
}

$report | Out-File -FilePath $reportFile -Encoding UTF8
Write-Host "`n报告已保存到: $reportFile" -ForegroundColor Cyan

# 生成CSV文件
$csvFile = Join-Path $basePath "00-内容深度评估列表-$(Get-Date -Format 'yyyy年MM月dd日').csv"
$results | Export-Csv -Path $csvFile -Encoding UTF8 -NoTypeInformation
Write-Host "CSV列表已保存到: $csvFile" -ForegroundColor Cyan
