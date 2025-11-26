# 锚点格式修复脚本
# 修复标题锚点格式，移除英文部分

$conceptFiles = Get-ChildItem "g:\_src\FormalMath\concept\核心概念\*.md" -Exclude "*三视角版*","*索引*","*关系*" | Sort-Object Name

foreach ($file in $conceptFiles) {
    Write-Host "处理文件: $($file.Name)"
    
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    
    # 修复标题锚点格式
    # 匹配格式: - [概念名称 (English Name)](#概念名称-english-name)
    # 改为: - [概念名称 (English Name)](#概念名称)
    
    # 提取中文标题部分
    if ($content -match "- \[([^\]]+)\s*\([^)]+\)\]\(#([^)]+)\)") {
        $titleLine = $content -split "`n" | Where-Object { $_ -match "^- \[.*\]\(#.*\)" } | Select-Object -First 1
        
        if ($titleLine -match "- \[([^\]]+)\s*\(([^)]+)\)\]\(#([^)]+)\)") {
            $chineseTitle = $matches[1].Trim()
            $englishTitle = $matches[2]
            $currentAnchor = $matches[3]
            
            # 生成新的锚点（只保留中文部分）
            $newAnchor = ($chineseTitle -replace "[^\w\s-]", "" -replace "\s+", "-").ToLower()
            $newAnchor = $newAnchor.Trim("-")
            
            if ($currentAnchor -ne $newAnchor) {
                $oldPattern = "- \[$chineseTitle\s*\($englishTitle\)\]\(#$currentAnchor\)"
                $newPattern = "- [$chineseTitle ($englishTitle)](#$newAnchor)"
                $content = $content -replace [regex]::Escape($oldPattern), $newPattern
                
                Set-Content -Path $file.FullName -Value $content -Encoding UTF8 -NoNewline
                Write-Host "已修复锚点: $($file.Name)"
            } else {
                Write-Host "锚点正确: $($file.Name)"
            }
        }
    }
}

Write-Host "`n所有文件处理完成！"
