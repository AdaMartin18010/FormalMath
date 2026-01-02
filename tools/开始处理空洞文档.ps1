# FormalMath项目开始处理空洞文档脚本
# 创建日期: 2025年12月31日
# 用途: 开始处理空洞文档，删除明显的模板文档

param(
    [switch]$DryRun,
    [switch]$Backup
)

$basePath = Split-Path -Parent $PSScriptRoot
$mathDir = Join-Path $basePath "数学家理念体系"

Write-Host "开始处理空洞文档..." -ForegroundColor Green

# 读取模板文档删除报告
$templateReport = Join-Path $basePath "00-模板文档删除报告-2026年01月01日.md"
$filesToDelete = @()

if (Test-Path $templateReport) {
    $reportContent = Get-Content -Path $templateReport -Raw -Encoding UTF8

    # 提取完全空文档
    $emptyMatches = [regex]::Matches($reportContent, '- \*\*([^\*]+)\*\*.*文件为空')
    foreach ($match in $emptyMatches) {
        $filePath = $match.Groups[1].Value.Trim()
        $fullPath = Join-Path $basePath $filePath
        if (Test-Path $fullPath) {
            $filesToDelete += @{
                File = $filePath
                FullPath = $fullPath
                Reason = "完全空文档"
                Priority = "P0"
            }
        }
    }

    # 提取模板文档（只处理明显的模板文档）
    $templateMatches = [regex]::Matches($reportContent, '- \*\*([^\*]+)\*\*.*类型: (Template|Shallow)')
    foreach ($match in $templateMatches) {
        $filePath = $match.Groups[1].Value.Trim()
        $fullPath = Join-Path $basePath $filePath

        # 只处理明显的模板文档（字数少于200的）
        if (Test-Path $fullPath) {
            try {
                $content = Get-Content -Path $fullPath -Raw -Encoding UTF8 -ErrorAction Stop
                $chineseChars = ([regex]::Matches($content, "[\u4e00-\u9fa5]")).Count
                $englishWords = ([regex]::Matches($content, "\b[a-zA-Z]{2,}\b")).Count
                $wordCount = $chineseChars + $englishWords

                # 只标记字数少于200的明显模板文档
                if ($wordCount -lt 200) {
                    $filesToDelete += @{
                        File = $filePath
                        FullPath = $fullPath
                        Reason = "模板文档（字数: $wordCount）"
                        Priority = "P0"
                    }
                }
            }
            catch {
                # 忽略读取错误
            }
        }
    }
}

Write-Host "`n找到 $($filesToDelete.Count) 个明显需要删除的文档" -ForegroundColor Cyan

# 生成删除列表报告
$deleteReportFile = Join-Path $basePath "00-待删除文档列表-$(Get-Date -Format 'yyyy年MM月dd日').md"
$report = @"
# 待删除文档列表

**生成日期**: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')
**状态**: 待审查

---

## 📊 统计信息

| 项目 | 数量 |
|------|------|
| 待删除文档总数 | $($filesToDelete.Count) |
| 完全空文档 | $($filesToDelete | Where-Object { $_.Reason -eq "完全空文档" }).Count |
| 模板文档（<200字） | $($filesToDelete | Where-Object { $_.Reason -match "模板文档" }).Count |

---

## 📝 待删除文档列表

"@

foreach ($item in ($filesToDelete | Sort-Object File)) {
    $report += "- **$($item.File)**`n"
    $report += "  - 原因: $($item.Reason)`n"
    $report += "  - 优先级: $($item.Priority)`n`n"
}

$report += @"

---

## ⚠️ 删除前检查

删除前请确认：
- [ ] 文档确实没有实质性内容
- [ ] 文档不在索引或导航中引用
- [ ] 删除不会影响其他文档

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$report | Out-File -FilePath $deleteReportFile -Encoding UTF8

Write-Host "`n处理完成!" -ForegroundColor Green
Write-Host "待删除文档数: $($filesToDelete.Count)" -ForegroundColor Yellow
Write-Host "报告已保存到: $deleteReportFile" -ForegroundColor Cyan

if ($DryRun) {
    Write-Host "`n这是试运行模式，未实际删除文件。" -ForegroundColor Yellow
    Write-Host "请审查报告后决定是否删除。" -ForegroundColor Yellow
} else {
    Write-Host "`n⚠️  警告: 未启用DryRun模式，但脚本不会自动删除文件。" -ForegroundColor Yellow
    Write-Host "请手动审查报告后决定是否删除。" -ForegroundColor Yellow
}
