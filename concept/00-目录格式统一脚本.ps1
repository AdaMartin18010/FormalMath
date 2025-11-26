# 目录格式统一脚本
# 将所有文件的目录格式统一为14-连续.md的格式

$templateFile = "g:\_src\FormalMath\concept\核心概念\14-连续.md"
$conceptFiles = Get-ChildItem "g:\_src\FormalMath\concept\核心概念\*.md" -Exclude "*三视角版*","*索引*","*关系*","14-连续.md" | Sort-Object Name

# 读取模板文件的目录格式
$templateContent = Get-Content $templateFile -Raw -Encoding UTF8
$templateTOC = ($templateContent -split "## 📑 目录")[1] -split "---" | Select-Object -First 1

Write-Host "模板目录格式已读取"

foreach ($file in $conceptFiles) {
    Write-Host "处理文件: $($file.Name)"
    
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    
    # 提取文件标题
    $titleMatch = $content -match "^# (.+?)\s*\("
    if ($titleMatch) {
        $title = ($content -split "`n" | Select-Object -First 1) -replace "^# ", "" -replace "\s*\(.*$", ""
        $fullTitle = ($content -split "`n" | Select-Object -First 1) -replace "^# ", ""
    } else {
        $title = $file.BaseName
        $fullTitle = $file.BaseName
    }
    
    # 提取所有章节标题
    $sections = @()
    $lines = $content -split "`n"
    
    foreach ($line in $lines) {
        if ($line -match "^##\s+([0-9]+)\.\s+(.+)$") {
            $num = $matches[1]
            $text = $matches[2].Trim()
            $anchor = ($text -replace "[^\w\s-]", "" -replace "\s+", "-").ToLower()
            $anchor = $anchor -replace "️", "" -replace "📋", "" -replace "🎯", "" -replace "📚", "" -replace "🔍", "" -replace "🔬", "" -replace "💡", "" -replace "🔗", "" -replace "📖", "" -replace "🗺️", "" -replace "📊", "" -replace "💭", "" -replace "👨‍🏫", "" -replace "🎨", "" -replace "📚", "" -replace "🎓", "" -replace "🧠", "" -replace "🧩", "" -replace "🧬", ""
            $anchor = $anchor.Trim("-")
            $sections += @{
                Level = 1
                Number = $num
                Text = $text
                Anchor = "$num-$anchor"
            }
        }
        elseif ($line -match "^###\s+([0-9]+\.[0-9]+)\s+(.+)$") {
            $num = $matches[1]
            $text = $matches[2].Trim()
            $anchor = ($text -replace "[^\w\s-]", "" -replace "\s+", "-").ToLower()
            $anchor = $anchor -replace "️", "" -replace "📋", "" -replace "🎯", "" -replace "📚", "" -replace "🔍", "" -replace "🔬", "" -replace "💡", "" -replace "🔗", "" -replace "📖", ""
            $anchor = $anchor.Trim("-")
            $sections += @{
                Level = 2
                Number = $num
                Text = $text
                Anchor = ($num -replace "\.", "") + "-" + $anchor
            }
        }
        elseif ($line -match "^####\s+(.+)$") {
            $text = $matches[1].Trim()
            $anchor = ($text -replace "[^\w\s-]", "" -replace "\s+", "-").ToLower()
            $anchor = $anchor.Trim("-")
            $sections += @{
                Level = 3
                Number = ""
                Text = $text
                Anchor = $anchor
            }
        }
    }
    
    # 生成新目录
    $newTOC = "## 📑 目录`n`n"
    $newTOC += "- [$fullTitle](#$($fullTitle -replace '[^\w\s-]', '' -replace '\s+', '-').ToLower())`n"
    $newTOC += "  - [📑 目录](#-目录)`n"
    
    $currentLevel1 = ""
    $currentLevel2 = ""
    
    foreach ($section in $sections) {
        if ($section.Level -eq 1) {
            $indent = "  "
            $newTOC += "$indent- [$($section.Number). $($section.Text)](#$($section.Anchor))`n"
            $currentLevel1 = $section.Number
            $currentLevel2 = ""
        }
        elseif ($section.Level -eq 2) {
            $indent = "    "
            $newTOC += "$indent- [$($section.Number) $($section.Text)](#$($section.Anchor))`n"
            $currentLevel2 = $section.Number
        }
        elseif ($section.Level -eq 3) {
            $indent = "      "
            $newTOC += "$indent- [$($section.Text)](#$($section.Anchor))`n"
        }
    }
    
    $newTOC += "`n---`n"
    
    # 替换目录部分
    if ($content -match "## 📑 目录") {
        $beforeTOC = ($content -split "## 📑 目录")[0]
        $afterTOC = ($content -split "## 📑 目录")[1]
        $afterTOC = ($afterTOC -split "---" | Select-Object -Skip 1) -join "---"
        
        $newContent = $beforeTOC + $newTOC + $afterTOC
        
        Set-Content -Path $file.FullName -Value $newContent -Encoding UTF8 -NoNewline
        Write-Host "已更新: $($file.Name)"
    } else {
        Write-Host "未找到目录: $($file.Name)"
    }
}

Write-Host "`n所有文件处理完成！"
