# FormalMath项目批量格式化P0文档脚本
# 创建日期: 2025年12月31日
# 用途: 批量格式化P0优先级文档

$basePath = Split-Path -Parent $PSScriptRoot
$formatted = 0
$skipped = 0
$errors = 0

Write-Host "开始批量格式化P0优先级文档..." -ForegroundColor Green

# P0优先级文档列表
$p0Files = @(
    "docs\01-基础数学\ZFC公理体系\数系与ZFC公理体系映射关系论证-国际标准版.md",
    "docs\01-基础数学\ZFC公理体系\ZFC公理体系到数论完整推导路径总结.md",
    "docs\01-基础数学\ZFC公理体系\Lean4形式化实现-ZFC公理体系.md",
    "docs\01-基础数学\ZFC公理体系\数系与ZFC公理体系映射关系分析-国际标准版.md",
    "docs\01-基础数学\ZFC公理体系\ZFC到数论完整推导-包含抽象代数结构.md",
    "docs\01-基础数学\集合论\01-集合论基础-国际标准版.md"
)

foreach ($filePath in $p0Files) {
    $fullPath = Join-Path $basePath $filePath

    if (-not (Test-Path $fullPath)) {
        Write-Host "⚠ 文件不存在: $filePath" -ForegroundColor Yellow
        $skipped++
        continue
    }

    try {
        # 检查是否已有元数据
        $content = Get-Content -Path $fullPath -Raw -Encoding UTF8
        if ($content -match "(创建日期|最后更新|制定日期|完成日期)") {
            Write-Host "✓ 已包含元数据，跳过: $filePath" -ForegroundColor Cyan
            $skipped++
            continue
        }

        # 获取文件信息
        $fileInfo = Get-Item $fullPath
        $createDate = $fileInfo.CreationTime.ToString("yyyy年MM月dd日")
        $lastUpdate = $fileInfo.LastWriteTime.ToString("yyyy年MM月dd日")

        # 获取文档标题
        $titleMatch = [regex]::Match($content, "^#\s+(.+)$", [System.Text.RegularExpressions.RegexOptions]::Multiline)
        $title = if ($titleMatch.Success) { $titleMatch.Groups[1].Value.Trim() } else { "文档标题" }

        # 构建新的文档头部
        $newHeader = @"
# $title

**创建日期**: $createDate
**最后更新**: $lastUpdate
**版本**: v1.0
**状态**: 完成

---

"@

        # 如果文档已有标题，在标题后添加元数据
        if ($titleMatch.Success) {
            $titleEndIndex = $titleMatch.Index + $titleMatch.Length
            $beforeTitle = $content.Substring(0, $titleEndIndex)
            $afterTitle = $content.Substring($titleEndIndex)

            # 移除标题后的空行（如果有）
            $afterTitle = $afterTitle -replace "^\s*\r?\n", ""

            # 构建新内容
            $newContent = $beforeTitle + "`n`n" + $newHeader + $afterTitle
        } else {
            # 如果没有标题，添加标题和元数据
            $newContent = $newHeader + $content
        }

        # 备份原文件
        $backupPath = $fullPath + ".bak"
        Copy-Item -Path $fullPath -Destination $backupPath -Force

        # 写入新内容
        $newContent | Out-File -FilePath $fullPath -Encoding UTF8 -NoNewline
        $formatted++
        Write-Host "✓ 已格式化: $filePath" -ForegroundColor Green
    } catch {
        $errors++
        Write-Host "✗ 错误: $filePath" -ForegroundColor Red
        Write-Host "  错误信息: $_" -ForegroundColor Red
    }
}

Write-Host "`n格式化完成:" -ForegroundColor Cyan
Write-Host "  已格式化: $formatted 个文件" -ForegroundColor Green
Write-Host "  已跳过: $skipped 个文件" -ForegroundColor Yellow
Write-Host "  错误: $errors 个" -ForegroundColor Red
