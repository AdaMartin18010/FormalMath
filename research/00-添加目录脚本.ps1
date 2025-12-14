# 为Markdown文档添加目录的PowerShell脚本
# 创建日期: 2025年11月30日

function Add-TOC-ToMarkdown {
    param(
        [string]$FilePath
    )

    $content = Get-Content -Path $FilePath -Raw -Encoding UTF8
    $lines = Get-Content -Path $FilePath -Encoding UTF8

    # 检查是否已有目录
    if ($content -match '## 📑 目录') {
        Write-Host "文件 $FilePath 已有目录，跳过" -ForegroundColor Yellow
        return
    }

    # 查找第一个一级标题的位置
    $firstHeadingIndex = -1
    for ($i = 0; $i -lt $lines.Count; $i++) {
        if ($lines[$i] -match '^##\s+[📋🎯📚✅❌🔍📖🔗📊📝🗓️]\s+[一二三四五六七八九十]+、') {
            $firstHeadingIndex = $i
            break
        }
    }

    if ($firstHeadingIndex -eq -1) {
        Write-Host "文件 $FilePath 未找到一级标题，跳过" -ForegroundColor Yellow
        return
    }

    # 提取所有标题
    $toc = @()
    $toc.Add("## 📑 目录")
    $toc.Add("")

    $currentLevel1 = 0
    $currentLevel2 = 0

    for ($i = $firstHeadingIndex; $i -lt $lines.Count; $i++) {
        $line = $lines[$i]

        # 一级标题 (## 📋 一、)
        if ($line -match '^##\s+[📋🎯📚✅❌🔍📖🔗📊📝🗓️]\s+([一二三四五六七八九十]+)、(.+)') {
            $currentLevel1++
            $currentLevel2 = 0
            $title = $matches[2].Trim()
            $anchor = $title -replace '\s+', '-' -replace '[()（）]', '' -replace '/', '-'
            $toc.Add("- [$($matches[1])、$title](#$anchor)")
        }
        # 二级标题 (### 1.1)
        elseif ($line -match '^###\s+(\d+)\.(\d+)\s+(.+)') {
            $currentLevel2++
            $title = $matches[3].Trim()
            $anchor = $title -replace '\s+', '-' -replace '[()（）]', '' -replace '/', '-'
            $toc.Add("  - [$($matches[1]).$($matches[2]) $title](#$($matches[1])$($matches[2])-$anchor)")
        }
    }

    $toc.Add("")
    $toc.Add("---")
    $toc.Add("")

    # 插入目录
    $newContent = @()
    for ($i = 0; $i -lt $firstHeadingIndex; $i++) {
        $newContent.Add($lines[$i])
    }

    $newContent.AddRange($toc)

    for ($i = $firstHeadingIndex; $i -lt $lines.Count; $i++) {
        $newContent.Add($lines[$i])
    }

    # 保存文件
    $newContent | Set-Content -Path $FilePath -Encoding UTF8 -NoNewline
    Write-Host "已为 $FilePath 添加目录" -ForegroundColor Green
}

# 获取所有需要处理的Markdown文件
$files = Get-ChildItem -Recurse -Filter "*.md" | Where-Object {
    $_.Name -notmatch 'README|总结|报告|规范|脚本' -and
    $_.FullName -notmatch '00-'
}

Write-Host "找到 $($files.Count) 个文件需要处理" -ForegroundColor Cyan

foreach ($file in $files) {
    Add-TOC-ToMarkdown -FilePath $file.FullName
}

Write-Host "`n处理完成！" -ForegroundColor Green
