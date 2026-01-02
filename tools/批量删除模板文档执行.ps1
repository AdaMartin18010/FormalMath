# FormalMath项目批量删除模板文档执行脚本
# 创建日期: 2026年01月01日
# 用途: 根据明显模板文档列表批量删除文档

param(
    [string]$ListFile,
    [int]$Limit = 0,
    [switch]$DryRun,
    [switch]$Backup
)

$basePath = Split-Path -Parent $PSScriptRoot

if ([string]::IsNullOrWhiteSpace($ListFile)) {
    $ListFile = Join-Path $basePath "00-明显模板文档列表-2026年01月01日.md"
}

Write-Host "开始批量删除模板文档..." -ForegroundColor Green
Write-Host "列表文件: $ListFile" -ForegroundColor Cyan

if (-not (Test-Path $ListFile)) {
    Write-Host "错误: 列表文件不存在！" -ForegroundColor Red
    exit 1
}

# 读取列表文件
$listContent = Get-Content -Path $ListFile -Raw -Encoding UTF8
$filesToDelete = @()

# 提取文档路径
$matches = [regex]::Matches($listContent, '### (数学家理念体系[^\n]+)')
foreach ($match in $matches) {
    $filePath = $match.Groups[1].Value.Trim()
    $fullPath = Join-Path $basePath $filePath

    if (Test-Path $fullPath) {
        $filesToDelete += @{
            File = $filePath
            FullPath = $fullPath
        }
    }
}

Write-Host "`n找到 $($filesToDelete.Count) 个待删除文档" -ForegroundColor Cyan

# 限制删除数量
if ($Limit -gt 0 -and $filesToDelete.Count -gt $Limit) {
    Write-Host "限制删除数量为: $Limit" -ForegroundColor Yellow
    $filesToDelete = $filesToDelete | Select-Object -First $Limit
}

# 执行删除
$deletedCount = 0
$failedCount = 0
$deletedFiles = @()

foreach ($file in $filesToDelete) {
    try {
        if ($Backup) {
            $backupPath = $file.FullPath + ".bak"
            Copy-Item -Path $file.FullPath -Destination $backupPath -Force -ErrorAction Stop
        }

        if (-not $DryRun) {
            Remove-Item -Path $file.FullPath -Force -ErrorAction Stop
            $deletedCount++
            $deletedFiles += $file.File
            Write-Host "  ✅ 已删除: $($file.File)" -ForegroundColor Green
        } else {
            Write-Host "  [试运行] 将删除: $($file.File)" -ForegroundColor Yellow
            $deletedCount++
        }
    }
    catch {
        $failedCount++
        Write-Host "  ❌ 删除失败: $($file.File) - $($_.Exception.Message)" -ForegroundColor Red
    }
}

# 生成删除报告
$reportFile = Join-Path $basePath "00-批量删除执行报告-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 批量删除执行报告

**执行日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**列表文件**: $ListFile

---

## 📊 执行统计

| 项目 | 数量 |
|------|------|
| 待删除文档数 | $($filesToDelete.Count) |
| 成功删除 | $deletedCount |
| 删除失败 | $failedCount |
| 限制数量 | $(if ($Limit -gt 0) { $Limit } else { "无限制" }) |

---

## 📝 已删除文档列表

"@

if ($deletedFiles.Count -gt 0) {
    foreach ($file in $deletedFiles) {
        $report += "- $file`n"
    }
} else {
    $report += "无文档被删除（试运行模式或删除失败）。`n"
}

$report += @"

---

## ⚙️ 执行参数

- **DryRun**: $(if ($DryRun) { "是" } else { "否" })
- **Backup**: $(if ($Backup) { "是" } else { "否" })
- **Limit**: $(if ($Limit -gt 0) { $Limit } else { "无限制" })

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$report | Out-File -FilePath $reportFile -Encoding UTF8

Write-Host "`n执行完成!" -ForegroundColor Green
Write-Host "成功删除: $deletedCount" -ForegroundColor Green
Write-Host "删除失败: $failedCount" -ForegroundColor $(if ($failedCount -gt 0) { "Red" } else { "Green" })
Write-Host "报告已保存到: $reportFile" -ForegroundColor Cyan

if ($DryRun) {
    Write-Host "`n这是试运行模式，未实际删除文件。" -ForegroundColor Yellow
}
