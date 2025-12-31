# FormalMath项目目录结构检查脚本
# 创建日期: 2025年12月29日
# 用途: 检查目录结构是否符合规范

param(
    [string]$Path = ".",
    [switch]$Recurse
)

# 统计信息
$stats = @{
    Total = 0
    Valid = 0
    Invalid = 0
    Errors = @()
    Warnings = @()
}

# 检查目录结构
function Test-DirectoryStructure {
    param([System.IO.DirectoryInfo]$Directory)

    $stats.Total++
    $errors = @()
    $warnings = @()

    # 检查目录命名
    $dirName = $Directory.Name

    # 检查禁止字符
    if ($dirName -match "[<>:""/\\|?*\s]") {
        $errors += "目录名包含禁止字符"
    }

    # 检查长度
    if ($dirName.Length -gt 50) {
        $errors += "目录名过长 ($($dirName.Length) > 50)"
    }

    # 检查嵌套深度
    $depth = ($Directory.FullName -replace [regex]::Escape($PWD.Path), "").Split('\').Count - 1
    if ($depth -gt 5) {
        $warnings += "目录嵌套过深 ($depth > 5)"
    }

    # 检查必需文件（根目录和主要模块）
    if ($depth -le 2) {
        $hasReadme = (Get-ChildItem -Path $Directory.FullName -Filter "README.md" -ErrorAction SilentlyContinue) -ne $null
        if (-not $hasReadme) {
            $warnings += "缺少README.md文件"
        }
    }

    # 检查编号连续性（对于数字前缀的目录）
    if ($dirName -match "^\d{2}-") {
        $subDirs = Get-ChildItem -Path $Directory.FullName -Directory -ErrorAction SilentlyContinue |
            Where-Object { $_.Name -match "^\d{2}-" } |
            Sort-Object Name

        if ($subDirs.Count -gt 1) {
            $numbers = $subDirs | ForEach-Object {
                if ($_.Name -match "^(\d{2})-") {
                    [int]$matches[1]
                }
            }

            $prevNum = $numbers[0]
            foreach ($num in $numbers[1..($numbers.Count-1)]) {
                if ($num -ne $prevNum + 1 -and $num -ne $prevNum + 10) {
                    $warnings += "目录编号不连续: $prevNum -> $num"
                }
                $prevNum = $num
            }
        }
    }

    if ($errors.Count -eq 0) {
        $stats.Valid++
    } else {
        $stats.Invalid++
        $stats.Errors += [PSCustomObject]@{
            Directory = $Directory.FullName
            Errors = $errors -join "; "
        }
    }

    if ($warnings.Count -gt 0) {
        $stats.Warnings += [PSCustomObject]@{
            Directory = $Directory.FullName
            Warnings = $warnings -join "; "
        }
    }
}

# 主程序
Write-Host "开始检查目录结构规范..." -ForegroundColor Green
Write-Host "检查路径: $Path" -ForegroundColor Cyan
Write-Host "递归检查: $Recurse" -ForegroundColor Cyan
Write-Host ""

# 获取目录列表
$directories = Get-ChildItem -Path $Path -Directory -Recurse:$Recurse

foreach ($dir in $directories) {
    # 跳过归档目录和隐藏目录
    if ($dir.Name -match "^\." -or $dir.Name -match "00-归档|99-归档|node_modules|\.git") {
        continue
    }

    Test-DirectoryStructure -Directory $dir
}

# 输出结果
Write-Host "`n检查完成!" -ForegroundColor Green
Write-Host "总目录数: $($stats.Total)" -ForegroundColor Cyan
Write-Host "符合规范: $($stats.Valid)" -ForegroundColor Green
Write-Host "不符合规范: $($stats.Invalid)" -ForegroundColor Red
Write-Host "警告: $($stats.Warnings.Count)" -ForegroundColor Yellow

if ($stats.Invalid -gt 0) {
    Write-Host "`n不符合规范的目录:" -ForegroundColor Yellow
    $stats.Errors | ForEach-Object {
        Write-Host "  - $($_.Directory)" -ForegroundColor Red
        Write-Host "    错误: $($_.Errors)" -ForegroundColor Red
    }
}

if ($stats.Warnings.Count -gt 0) {
    Write-Host "`n警告:" -ForegroundColor Yellow
    $stats.Warnings | ForEach-Object {
        Write-Host "  - $($_.Directory)" -ForegroundColor Yellow
        Write-Host "    警告: $($_.Warnings)" -ForegroundColor Yellow
    }
}

# 生成报告文件
$reportFile = "00-结构检查报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 目录结构检查报告

**检查日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**检查路径**: $Path
**递归检查**: $Recurse

## 统计信息

| 项目 | 数量 |
|------|------|
| 总目录数 | $($stats.Total) |
| 符合规范 | $($stats.Valid) |
| 不符合规范 | $($stats.Invalid) |
| 警告 | $($stats.Warnings.Count) |

"@

if ($stats.Invalid -gt 0) {
    $report += "`n## 不符合规范的目录列表`n`n"
    $stats.Errors | ForEach-Object {
        $report += "### $($_.Directory)`n`n"
        $report += "- **错误**: $($_.Errors)`n`n"
    }
}

if ($stats.Warnings.Count -gt 0) {
    $report += "`n## 警告列表`n`n"
    $stats.Warnings | ForEach-Object {
        $report += "### $($_.Directory)`n`n"
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
