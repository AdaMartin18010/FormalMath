# 文件结构遗漏部分修复脚本
# 修复所有遗漏编号的部分

$conceptFiles = Get-ChildItem "g:\_src\FormalMath\concept\核心概念\*.md" -Exclude "*三视角版*","*索引*","*关系*" | Sort-Object Name

foreach ($file in $conceptFiles) {
    Write-Host "检查文件: $($file.Name)"
    
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $modified = $false
    
    # 修复遗漏编号的其他部分
    if ($content -match '## 👨‍🏫 专家观点与论证' -and $content -notmatch '## 9\.[0-9] 👨‍🏫') {
        $content = $content -replace '## 👨‍🏫 专家观点与论证', '## 9.6 👨‍🏫 专家观点与论证'
        $modified = $true
    }
    if ($content -match '## 🎨 认知维度表征' -and $content -notmatch '## 9\.[0-9] 🎨') {
        $content = $content -replace '## 🎨 认知维度表征', '## 9.7 🎨 认知维度表征'
        $modified = $true
    }
    if ($content -match '## 🧠 认知维度表征' -and $content -notmatch '## 9\.[0-9] 🧠') {
        $content = $content -replace '## 🧠 认知维度表征', '## 9.6 🧠 认知维度表征'
        $modified = $true
    }
    if ($content -match '## 🧩 理性维度表征' -and $content -notmatch '## 9\.[0-9] 🧩') {
        $content = $content -replace '## 🧩 理性维度表征', '## 9.7 🧩 理性维度表征'
        $modified = $true
    }
    if ($content -match '## 🧬 综合整合表征' -and $content -notmatch '## 9\.[0-9] 🧬') {
        $content = $content -replace '## 🧬 综合整合表征', '## 9.8 🧬 综合整合表征'
        $modified = $true
    }
    
    # 更新目录中的链接（如果有这些部分）
    if ($content -match '## 9\.6 👨‍🏫' -and $content -notmatch '9\.6 \[专家观点与论证\]') {
        # 在目录中添加9.6链接
        if ($content -match '9\.5 \[习题库\]') {
            $content = $content -replace '(9\.5 \[习题库\]\(#95-习题库\)（如果有）)', "`$1`n   - 9.6 [专家观点与论证](#96-专家观点与论证)（如果有）"
            $modified = $true
        }
    }
    if ($content -match '## 9\.7 🎨' -and $content -notmatch '9\.7 \[认知维度表征\]') {
        # 在目录中添加9.7链接
        if ($content -match '9\.6 \[专家观点与论证\]') {
            $content = $content -replace '(9\.6 \[专家观点与论证\]\(#96-专家观点与论证\)（如果有）)', "`$1`n   - 9.7 [认知维度表征](#97-认知维度表征)（如果有）"
            $modified = $true
        }
    }
    
    if ($modified) {
        Set-Content -Path $file.FullName -Value $content -Encoding UTF8 -NoNewline
        Write-Host "已修复: $($file.Name)"
    } else {
        Write-Host "无需修复: $($file.Name)"
    }
}

Write-Host "`n所有文件检查完成！"
