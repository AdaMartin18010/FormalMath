# FormalMath项目文档头部格式化脚本
# 创建日期: 2025年12月31日
# 用途: 为文档添加标准头部格式

param(
    [string]$FilePath,
    [string]$CreateDate = "",
    [string]$LastUpdate = "",
    [string]$Version = "v1.0",
    [string]$Status = "完成"
)

if (-not $FilePath) {
    Write-Host "用法: .\格式化文档头部.ps1 -FilePath <文件路径> [-CreateDate <日期>] [-LastUpdate <日期>] [-Version <版本>] [-Status <状态>]" -ForegroundColor Yellow
    exit 1
}

if (-not (Test-Path $FilePath)) {
    Write-Host "文件不存在: $FilePath" -ForegroundColor Red
    exit 1
}

$content = Get-Content -Path $FilePath -Raw -Encoding UTF8
$lines = Get-Content -Path $FilePath -Encoding UTF8

# 检查是否已有元数据
$hasMetadata = $content -match "(创建日期|最后更新|制定日期|完成日期|创建日期|版本|状态)"

# 获取文档标题（第一个一级标题）
$titleMatch = [regex]::Match($content, "^#\s+(.+)$", [System.Text.RegularExpressions.RegexOptions]::Multiline)
$title = if ($titleMatch.Success) { $titleMatch.Groups[1].Value.Trim() } else { "文档标题" }

# 如果没有创建日期，使用文件创建时间
if (-not $CreateDate) {
    $fileInfo = Get-Item $FilePath
    $CreateDate = $fileInfo.CreationTime.ToString("yyyy年MM月dd日")
}

# 如果没有最后更新日期，使用文件修改时间
if (-not $LastUpdate) {
    $fileInfo = Get-Item $FilePath
    $LastUpdate = $fileInfo.LastWriteTime.ToString("yyyy年MM月dd日")
}

# 构建新的文档头部
$newHeader = @"
# $title

**创建日期**: $CreateDate
**最后更新**: $LastUpdate
**版本**: $Version
**状态**: $Status

---

"@

# 如果文档已有标题但没有元数据，在标题后添加元数据
if ($titleMatch.Success -and -not $hasMetadata) {
    # 找到标题后的位置
    $titleEndIndex = $titleMatch.Index + $titleMatch.Length
    $beforeTitle = $content.Substring(0, $titleEndIndex)
    $afterTitle = $content.Substring($titleEndIndex)

    # 移除标题后的空行（如果有）
    $afterTitle = $afterTitle -replace "^\s*\r?\n", ""

    # 构建新内容
    $newContent = $beforeTitle + "`n`n" + $newHeader + $afterTitle
} elseif (-not $titleMatch.Success) {
    # 如果没有标题，添加标题和元数据
    $newContent = $newHeader + $content
} else {
    # 如果已有元数据，不修改
    Write-Host "文档已包含元数据，跳过: $FilePath" -ForegroundColor Yellow
    exit 0
}

# 备份原文件
$backupPath = $FilePath + ".bak"
Copy-Item -Path $FilePath -Destination $backupPath -Force
Write-Host "已备份原文件到: $backupPath" -ForegroundColor Cyan

# 写入新内容
$newContent | Out-File -FilePath $FilePath -Encoding UTF8 -NoNewline
Write-Host "✓ 已格式化: $FilePath" -ForegroundColor Green
