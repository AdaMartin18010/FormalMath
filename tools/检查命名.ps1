# FormalMath项目文件命名检查脚本
# 创建日期: 2025年12月29日
# 用途: 检查文件命名是否符合规范

param(
    [string]$Path = ".",
    [switch]$Recurse,
    [switch]$Fix
)

# 命名规范规则
$rules = @{
    "管理文档前缀" = "^00-"
    "内容文档前缀" = "^\d{2}-"
    "禁止字符" = "[<>:""/\\|?*\s]"
    "最大长度" = 50
}

# 统计信息
$stats = @{
    Total = 0
    Valid = 0
    Invalid = 0
    Errors = @()
}

# 检查文件命名
function Test-FileName {
    param([string]$FileName, [string]$FullPath)

    $stats.Total++
    $errors = @()

    # 检查禁止字符
    if ($FileName -match $rules["禁止字符"]) {
        $errors += "包含禁止字符"
    }

    # 检查长度
    if ($FileName.Length -gt $rules["最大长度"]) {
        $errors += "文件名过长 ($($FileName.Length) > $($rules["最大长度"]))"
    }

    # 检查前缀（仅对.md文件）
    if ($FileName -match "\.md$") {
        $baseName = $FileName -replace "\.md$", ""

        # 管理文档检查
        if ($baseName -match "^00-") {
            # 管理文档格式: 00-[文档类型]-[日期].md
            # 允许更灵活的文档类型名称
            if ($baseName -notmatch "^00-(项目状态|文档索引|README|完成报告|进度报告|工作总结|执行计划|评价报告|归档索引|全面任务梳理|理解认知表征|文档清理|阶段完成总结|Week\d+完成总结|P\d+级项目|项目全面|项目后续|项目持续|项目改进)(-[\d年月日-]+)?$") {
                # 如果不符合标准格式，检查是否至少符合基本格式（00-开头，包含合理字符）
                if ($baseName -notmatch "^00-[^<>:""/\\|?*\s]+$") {
                    $errors += "管理文档命名格式不正确"
                }
            }
        }
        # 内容文档检查
        elseif ($baseName -match "^\d{2}-") {
            # 内容文档格式: [序号]-[文档标题].md
            if ($baseName -notmatch "^\d{2}-.+") {
                $errors += "内容文档命名格式不正确"
            }
        }
        # README文件例外
        elseif ($FileName -eq "README.md") {
            # README文件允许
        }
        else {
            $errors += "缺少标准前缀（00-或数字前缀）"
        }
    }

    if ($errors.Count -eq 0) {
        $stats.Valid++
        return $true
    } else {
        $stats.Invalid++
        $stats.Errors += [PSCustomObject]@{
            File = $FullPath
            Errors = $errors -join "; "
        }
        return $false
    }
}

# 主程序
Write-Host "开始检查文件命名规范..." -ForegroundColor Green
Write-Host "检查路径: $Path" -ForegroundColor Cyan
Write-Host "递归检查: $Recurse" -ForegroundColor Cyan
Write-Host ""

# 获取文件列表
$files = Get-ChildItem -Path $Path -Filter "*.md" -Recurse:$Recurse -File

foreach ($file in $files) {
    # 跳过归档目录
    if ($file.FullName -match "00-归档|99-归档") {
        continue
    }

    Test-FileName -FileName $file.Name -FullPath $file.FullName
}

# 输出结果
Write-Host "`n检查完成!" -ForegroundColor Green
Write-Host "总文件数: $($stats.Total)" -ForegroundColor Cyan
Write-Host "符合规范: $($stats.Valid)" -ForegroundColor Green
Write-Host "不符合规范: $($stats.Invalid)" -ForegroundColor Red

if ($stats.Invalid -gt 0) {
    Write-Host "`n不符合规范的文件:" -ForegroundColor Yellow
    $stats.Errors | ForEach-Object {
        Write-Host "  - $($_.File)" -ForegroundColor Red
        Write-Host "    错误: $($_.Errors)" -ForegroundColor Red
    }

    # 生成报告文件
    $reportFile = "00-命名检查报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
    $report = @"
# 文件命名检查报告

**检查日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**检查路径**: $Path
**递归检查**: $Recurse

## 统计信息

| 项目 | 数量 |
|------|------|
| 总文件数 | $($stats.Total) |
| 符合规范 | $($stats.Valid) |
| 不符合规范 | $($stats.Invalid) |

## 不符合规范的文件列表

"@

    $stats.Errors | ForEach-Object {
        $report += "`n### $($_.File)`n`n"
        $report += "- **错误**: $($_.Errors)`n"
    }

    $report | Out-File -FilePath $reportFile -Encoding UTF8
    Write-Host "`n报告已保存到: $reportFile" -ForegroundColor Cyan
}

if ($stats.Invalid -gt 0) {
    exit 1
} else {
    exit 0
}
