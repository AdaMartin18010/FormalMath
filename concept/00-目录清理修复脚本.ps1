# 目录清理修复脚本
# 清理所有文件中的重复目录和格式错误

$conceptFiles = Get-ChildItem "g:\_src\FormalMath\concept\核心概念\*.md" -Exclude "*三视角版*","*索引*","*关系*" | Sort-Object Name

foreach ($file in $conceptFiles) {
    Write-Host "检查文件: $($file.Name)"
    
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $lines = $content -split "`n"
    
    # 找到第一个目录的结束位置（第一个---之后）
    $tocStartIndex = -1
    $tocEndIndex = -1
    $firstDashDashDash = -1
    
    for ($i = 0; $i -lt $lines.Length; $i++) {
        if ($lines[$i] -match "^## 📑 目录") {
            $tocStartIndex = $i
        }
        if ($tocStartIndex -ge 0 -and $lines[$i] -match "^---$" -and $firstDashDashDash -eq -1) {
            $firstDashDashDash = $i
            $tocEndIndex = $i
            break
        }
    }
    
    if ($tocStartIndex -ge 0 -and $tocEndIndex -ge 0) {
        # 检查是否有重复的目录内容
        $hasDuplicate = $false
        $duplicateStart = -1
        
        # 查找第一个---之后是否还有目录相关的内容
        for ($i = $firstDashDashDash + 1; $i -lt [Math]::Min($firstDashDashDash + 100, $lines.Length); $i++) {
            if ($lines[$i] -match "^---rsa|^---$" -or 
                ($lines[$i] -match "^-\s*\[7\." -and $lines[$i+1] -match "^-\s*\[8\.")) {
                $hasDuplicate = $true
                $duplicateStart = $i
                break
            }
        }
        
        if ($hasDuplicate) {
            Write-Host "发现重复内容，开始清理: $($file.Name)"
            
            # 找到第一个真正的章节标题（## 1. 或 ## 1）
            $firstSectionIndex = -1
            for ($i = $firstDashDashDash + 1; $i -lt $lines.Length; $i++) {
                if ($lines[$i] -match "^##\s+[0-9]+\.") {
                    $firstSectionIndex = $i
                    break
                }
            }
            
            if ($firstSectionIndex -gt $firstDashDashDash) {
                # 保留目录部分和第一个---，删除之间的所有内容
                $beforeTOC = ($lines[0..$firstDashDashDash] -join "`n") + "`n"
                $afterTOC = ""
                
                # 找到第一个真正的章节标题
                for ($i = $firstDashDashDash + 1; $i -lt $lines.Length; $i++) {
                    if ($lines[$i] -match "^##\s+[0-9]+\.") {
                        $afterTOC = ($lines[$i..($lines.Length-1)] -join "`n")
                        break
                    }
                }
                
                if ($afterTOC -eq "") {
                    $afterTOC = ($lines[($firstDashDashDash+1)..($lines.Length-1)] -join "`n")
                }
                
                $newContent = $beforeTOC + "`n" + $afterTOC
                
                Set-Content -Path $file.FullName -Value $newContent -Encoding UTF8 -NoNewline
                Write-Host "已清理: $($file.Name)"
            }
        } else {
            Write-Host "无需清理: $($file.Name)"
        }
    } else {
        Write-Host "未找到目录: $($file.Name)"
    }
}

Write-Host "`n所有文件检查完成！"
