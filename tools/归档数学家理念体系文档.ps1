# FormalMath项目数学家理念体系目录文档归档脚本
# 创建日期: 2025年12月31日
# 用途: 归档重复的完成报告、总结报告等历史版本

$basePath = Split-Path -Parent $PSScriptRoot
$mathPath = Join-Path $basePath "数学家理念体系"
$archivePath = Join-Path $mathPath "00-归档\2025年12月"

Write-Host "开始归档数学家理念体系目录文档..." -ForegroundColor Green
Write-Host "基础路径: $basePath" -ForegroundColor Cyan

# 定义要保留的最新文档（不归档）
$keepFiles = @(
    "00-最终完成确认-2025年12月28日.md",
    "00-未完成任务全面梳理-2025年12月28日.md",
    "00-任务梳理与推进执行报告-2025年12月11日.md",
    "00-内容质量提升最终完成报告-2025年12月.md",
    "00-内容质量提升进度报告-2025年12月.md",
    "00-内容质量提升完成报告-2025年12月.md",
    "00-内容质量提升计划-2025年12月.md",
    "00-内容质量提升最新进度-2025年12月.md",
    "00-项目状态总览-2025年12月15日.md",
    "00-项目状态总览-2025年12月11日.md",
    "00-项目文档索引-2025年12月11日.md",
    "00-项目完整统计报告-2025年12月11日.md",
    "00-数学家关联性分析.md",
    "00-数学家时间线索引.md",
    "00-数学思脉哲科关系分析.md",
    "00-ONLINE-RESOURCES-ALIGNMENT.md",
    "00-PHASE1-COMPLETION-SUMMARY.md",
    "00-PRIORITY-SCHEDULE.md",
    "00-PROJECT-MASTER-PLAN.md",
    "00-TASK-LIST-P0.md"
)

# 获取所有00-开头的文档
$allFiles = Get-ChildItem -Path $mathPath -Filter "00-*.md" -File

$archived = 0
$kept = 0
$errors = 0

foreach ($file in $allFiles) {
    $fileName = $file.Name

    # 检查是否应该保留
    if ($keepFiles -contains $fileName) {
        $kept++
        Write-Host "保留: $fileName" -ForegroundColor Cyan
        continue
    }

    # 判断文档类型并归档
    $targetDir = $null
    if ($fileName -match "完成报告|完成总结|完成确认|全部完成|全面完成") {
        $targetDir = Join-Path $archivePath "完成报告"
    } elseif ($fileName -match "总结|汇总") {
        $targetDir = Join-Path $archivePath "总结报告"
    } elseif ($fileName -match "推进|执行|计划|梳理") {
        $targetDir = Join-Path $archivePath "推进报告"
    } else {
        $targetDir = Join-Path $archivePath "其他报告"
    }

    try {
        # 确保目标目录存在
        if (-not (Test-Path $targetDir)) {
            New-Item -ItemType Directory -Path $targetDir -Force | Out-Null
        }

        # 移动文件
        $targetPath = Join-Path $targetDir $fileName
        if (Test-Path $targetPath) {
            # 如果目标文件已存在，添加时间戳
            $timestamp = Get-Date -Format "yyyyMMddHHmmss"
            $nameWithoutExt = [System.IO.Path]::GetFileNameWithoutExtension($fileName)
            $ext = [System.IO.Path]::GetExtension($fileName)
            $targetPath = Join-Path $targetDir "$nameWithoutExt-$timestamp$ext"
        }

        Move-Item -Path $file.FullName -Destination $targetPath -Force
        $archived++
        Write-Host "✓ 已归档: $fileName -> $targetDir" -ForegroundColor Green
    } catch {
        $errors++
        Write-Host "✗ 错误: $fileName" -ForegroundColor Red
        Write-Host "  错误信息: $_" -ForegroundColor Red
    }
}

Write-Host "`n归档完成:" -ForegroundColor Cyan
Write-Host "  已归档: $archived 个文件" -ForegroundColor Green
Write-Host "  已保留: $kept 个文件" -ForegroundColor Cyan
Write-Host "  错误: $errors 个" -ForegroundColor Red
