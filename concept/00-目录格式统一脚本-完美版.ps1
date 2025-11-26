# 目录格式统一脚本（完美版）
# 将所有文件的目录格式统一为14-连续.md的格式

$conceptFiles = Get-ChildItem "g:\_src\FormalMath\concept\核心概念\*.md" -Exclude "*三视角版*","*索引*","*关系*" | Sort-Object Name

foreach ($file in $conceptFiles) {
    Write-Host "处理文件: $($file.Name)"
    
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $lines = $content -split "`n"
    
    # 提取文件标题（第一行）
    $titleLine = $lines[0]
    if ($titleLine -match "^# (.+)$") {
        $fullTitle = $matches[1].Trim()
        # 生成锚点：移除括号内容，转换为小写，替换空格为连字符
        $titleAnchor = ($fullTitle -replace "\s*\([^)]+\)", "" -replace "[^\w\s-]", "" -replace "\s+", "-").ToLower()
        $titleAnchor = $titleAnchor.Trim("-")
    } else {
        $fullTitle = $file.BaseName
        $titleAnchor = ($file.BaseName -replace "[^\w\s-]", "" -replace "\s+", "-").ToLower()
    }
    
    # 提取所有章节
    $sections = @()
    foreach ($line in $lines) {
        $trimmed = $line.Trim()
        
        # 匹配 ## 1. 📋 概述 格式
        if ($trimmed -match "^##\s+([0-9]+)\.\s+(.+)$") {
            $num = $matches[1]
            $text = $matches[2].Trim()
            # 移除编号部分
            $text = $text -replace "\s*\(编号:.*?\)", ""
            $anchor = ($text -replace "[^\w\s-]", "" -replace "\s+", "-").ToLower()
            $anchor = $anchor.Trim("-")
            if ($anchor) {
                $sections += @{
                    Level = 1
                    Number = $num
                    Text = $text
                    Anchor = "$num-$anchor"
                }
            }
        }
        # 匹配 ### 2.1 基础定义 (L0) 格式
        elseif ($trimmed -match "^###\s+([0-9]+\.[0-9]+)\s+(.+)$") {
            $num = $matches[1]
            $text = $matches[2].Trim()
            $text = $text -replace "\s*\(编号:.*?\)", ""
            $anchor = ($text -replace "[^\w\s-]", "" -replace "\s+", "-").ToLower()
            $anchor = $anchor.Trim("-")
            if ($anchor) {
                $sections += @{
                    Level = 2
                    Number = $num
                    Text = $text
                    Anchor = ($num -replace "\.", "") + "-" + $anchor
                }
            }
        }
        # 匹配 ### 依赖关系 格式（没有编号的###）
        elseif ($trimmed -match "^###\s+([^0-9].+)$") {
            $text = $matches[1].Trim()
            # 跳过编号行和空行
            if ($text -notmatch "编号:" -and $text -ne "") {
                $anchor = ($text -replace "[^\w\s-]", "" -replace "\s+", "-").ToLower()
                $anchor = $anchor.Trim("-")
                if ($anchor) {
                    $sections += @{
                        Level = 2
                        Number = ""
                        Text = $text
                        Anchor = $anchor
                    }
                }
            }
        }
        # 匹配 #### 应用1: 格式
        elseif ($trimmed -match "^####\s+(.+)$") {
            $text = $matches[1].Trim()
            # 跳过编号行
            if ($text -notmatch "编号:" -and $text -ne "") {
                $anchor = ($text -replace "[^\w\s-]", "" -replace "\s+", "-").ToLower()
                $anchor = $anchor.Trim("-")
                if ($anchor) {
                    $sections += @{
                        Level = 3
                        Number = ""
                        Text = $text
                        Anchor = $anchor
                    }
                }
            }
        }
    }
    
    # 生成新目录
    $newTOC = "## 📑 目录`n`n"
    $newTOC += "- [$fullTitle](#$titleAnchor)`n"
    $newTOC += "  - [📑 目录](#-目录)`n"
    
    foreach ($section in $sections) {
        if ($section.Level -eq 1) {
            $indent = "  "
            $newTOC += "$indent- [$($section.Number). $($section.Text)](#$($section.Anchor))`n"
        }
        elseif ($section.Level -eq 2) {
            $indent = "    "
            # 如果有编号，显示编号；否则只显示文本
            if ($section.Number -ne "") {
                $newTOC += "$indent- [$($section.Number) $($section.Text)](#$($section.Anchor))`n"
            } else {
                $newTOC += "$indent- [$($section.Text)](#$($section.Anchor))`n"
            }
        }
        elseif ($section.Level -eq 3) {
            $indent = "      "
            $newTOC += "$indent- [$($section.Text)](#$($section.Anchor))`n"
        }
    }
    
    $newTOC += "`n---`n"
    
    # 替换目录部分
    if ($content -match "## 📑 目录") {
        $parts = $content -split "## 📑 目录", 2
        $beforeTOC = $parts[0]
        $afterTOC = $parts[1]
        
        # 找到第一个 --- 之后的内容
        $afterParts = $afterTOC -split "---", 2
        if ($afterParts.Length -gt 1) {
            $afterTOC = "---" + $afterParts[1]
        } else {
            # 如果没有找到---，尝试找到第一个##标题
            $afterTOC = ($afterTOC -split "##", 2)[1]
            if ($afterTOC) {
                $afterTOC = "##" + $afterTOC
            }
        }
        
        $newContent = $beforeTOC + $newTOC + $afterTOC
        
        Set-Content -Path $file.FullName -Value $newContent -Encoding UTF8 -NoNewline
        Write-Host "已更新: $($file.Name)"
    } else {
        Write-Host "未找到目录: $($file.Name)"
    }
}

Write-Host "`n所有文件处理完成！"
