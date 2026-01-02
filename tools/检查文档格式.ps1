# FormalMath项目文档格式检查脚本
# 创建日期: 2025年12月31日
# 用途: 检查文档格式是否符合规范

param(
    [string]$Path = ".",
    [string[]]$Include = @("*.md"),
    [switch]$Recurse
)

$basePath = Split-Path -Parent $PSScriptRoot
$checkPath = if ($Path -eq ".") { $basePath } else { Join-Path $basePath $Path }

Write-Host "开始检查文档格式..." -ForegroundColor Green
Write-Host "检查路径: $checkPath" -ForegroundColor Cyan

$stats = @{
    Total = 0
    Valid = 0
    Invalid = 0
    Errors = @()
    Warnings = @()
}

function Test-DocumentFormat {
    param([System.IO.FileInfo]$File)

    $stats.Total++
    $errors = @()
    $warnings = @()
    $content = Get-Content -Path $File.FullName -Raw -Encoding UTF8

    # 检查文档头部
    if (-not ($content -match "^#\s+.+")) {
        $errors += "缺少文档标题（一级标题）"
    }

    # 检查是否有元数据（日期、版本等）
    if (-not ($content -match "(创建日期|最后更新|制定日期|完成日期)")) {
        $warnings += "缺少元数据（日期信息）"
    }

    # 检查标题层级
    $h1Count = ([regex]::Matches($content, "^#\s+")).Count
    if ($h1Count -ne 1) {
        $warnings += "一级标题数量: $h1Count (应为1个)"
    }

    # 检查是否有分隔线
    if (-not ($content -match "^---")) {
        $warnings += "缺少分隔线（---）"
    }

    # 检查列表格式（应该使用-而不是*）
    if ($content -match "^\*\s+") {
        $warnings += "使用了*作为列表标记（应使用-）"
    }

    # 检查表格格式
    if ($content -match "\|.*\|") {
        # 检查表格前后是否有空行
        $tableLines = [regex]::Matches($content, "^\|.*\|$", [System.Text.RegularExpressions.RegexOptions]::Multiline)
        foreach ($match in $tableLines) {
            $lineNum = ($content.Substring(0, $match.Index) -split "`n").Count
            # 这里可以添加更详细的表格格式检查
        }
    }

    # 检查代码块格式
    $codeBlockPattern = '```'
    if ($content -match $codeBlockPattern) {
        $codeBlocks = [regex]::Matches($content, $codeBlockPattern)
        if ($codeBlocks.Count % 2 -ne 0) {
            $errors += "代码块未正确闭合"
        }
    }

    if ($errors.Count -eq 0 -and $warnings.Count -eq 0) {
        $stats.Valid++
    } else {
        if ($errors.Count -gt 0) {
            $stats.Invalid++
            $stats.Errors += [PSCustomObject]@{
                File = $File.FullName
                Errors = $errors -join "; "
            }
        }
        if ($warnings.Count -gt 0) {
            $stats.Warnings += [PSCustomObject]@{
                File = $File.FullName
                Warnings = $warnings -join "; "
            }
        }
    }
}

# 获取文件列表
if ($Include.Count -eq 1 -and $Include[0] -eq "*.md") {
    $files = Get-ChildItem -Path $checkPath -Filter "*.md" -Recurse:$Recurse -File |
        Where-Object {
            $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git)" -and
            $_.Name -match "^00-Week"
        }
} else {
    $files = Get-ChildItem -Path $checkPath -Include $Include -Recurse:$Recurse -File |
        Where-Object { $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git)" }
}

foreach ($file in $files) {
    Test-DocumentFormat -File $file
}

# 输出结果
Write-Host "`n检查完成!" -ForegroundColor Green
Write-Host "总文件数: $($stats.Total)" -ForegroundColor Cyan
Write-Host "符合规范: $($stats.Valid)" -ForegroundColor Green
Write-Host "不符合规范: $($stats.Invalid)" -ForegroundColor Red
Write-Host "警告: $($stats.Warnings.Count)" -ForegroundColor Yellow

if ($stats.Invalid -gt 0) {
    Write-Host "`n不符合规范的文档:" -ForegroundColor Yellow
    $stats.Errors | Select-Object -First 10 | ForEach-Object {
        Write-Host "  - $($_.File)" -ForegroundColor Red
        Write-Host "    错误: $($_.Errors)" -ForegroundColor Red
    }
    if ($stats.Errors.Count -gt 10) {
        Write-Host "  ... 还有 $($stats.Errors.Count - 10) 个文档" -ForegroundColor Yellow
    }
}

if ($stats.Warnings.Count -gt 0) {
    Write-Host "`n警告（前10个）:" -ForegroundColor Yellow
    $stats.Warnings | Select-Object -First 10 | ForEach-Object {
        Write-Host "  - $($_.File)" -ForegroundColor Yellow
        Write-Host "    警告: $($_.Warnings)" -ForegroundColor Yellow
    }
    if ($stats.Warnings.Count -gt 10) {
        Write-Host "  ... 还有 $($stats.Warnings.Count - 10) 个文档" -ForegroundColor Yellow
    }
}

# 生成报告
$reportFile = Join-Path $basePath "00-格式检查报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 文档格式检查报告

**检查日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**检查路径**: $checkPath
**递归检查**: $Recurse

## 统计信息

| 项目 | 数量 |
|------|------|
| 总文件数 | $($stats.Total) |
| 符合规范 | $($stats.Valid) |
| 不符合规范 | $($stats.Invalid) |
| 警告 | $($stats.Warnings.Count) |

"@

if ($stats.Invalid -gt 0) {
    $report += "`n## 不符合规范的文档列表`n`n"
    $stats.Errors | ForEach-Object {
        $relativePath = $_.File.Replace($basePath, "").TrimStart('\')
        $report += "### $relativePath`n`n"
        $report += "- **错误**: $($_.Errors)`n`n"
    }
}

if ($stats.Warnings.Count -gt 0) {
    $report += "`n## 警告列表`n`n"
    $stats.Warnings | Select-Object -First 20 | ForEach-Object {
        $relativePath = $_.File.Replace($basePath, "").TrimStart('\')
        $report += "### $relativePath`n`n"
        $report += "- **警告**: $($_.Warnings)`n`n"
    }
}

$report | Out-File -FilePath $reportFile -Encoding UTF8
Write-Host "`n报告已保存到: $reportFile" -ForegroundColor Cyan

if ($stats.Invalid -gt 0) {
    exit 1
} else {
    exit 0
}
