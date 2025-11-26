# 文件结构编号顺序修复脚本
# 重新整理其他部分的编号顺序

$conceptFiles = Get-ChildItem "g:\_src\FormalMath\concept\核心概念\*.md" -Exclude "*三视角版*","*索引*","*关系*" | Sort-Object Name

foreach ($file in $conceptFiles) {
    Write-Host "修复文件: $($file.Name)"
    
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $modified = $false
    
    # 标准顺序：
    # 9.1 思维导图
    # 9.2 知识多维关系矩阵
    # 9.3 形象化解释与论证
    # 9.4 学习路径
    # 9.5 习题库
    # 9.6 专家观点与论证
    # 9.7 认知维度表征
    # 9.8 理性维度表征
    # 9.9 综合整合表征
    
    # 修复编号顺序（先修复后面的，避免冲突）
    if ($content -match '## 9\.9') {
        # 如果已经有9.9，保持不变
    } elseif ($content -match '## 🧬 综合整合表征' -and $content -notmatch '## 9\.9 🧬') {
        $content = $content -replace '## 9\.8 🧬 综合整合表征', '## 9.9 🧬 综合整合表征'
        $content = $content -replace '## 🧬 综合整合表征', '## 9.9 🧬 综合整合表征'
        $modified = $true
    }
    
    if ($content -match '## 🧩 理性维度表征' -and $content -notmatch '## 9\.8 🧩') {
        $content = $content -replace '## 9\.7 🧩 理性维度表征', '## 9.8 🧩 理性维度表征'
        $content = $content -replace '## 🧩 理性维度表征', '## 9.8 🧩 理性维度表征'
        $modified = $true
    }
    
    if ($content -match '## 🎨 认知维度表征' -and $content -notmatch '## 9\.7 🎨') {
        $content = $content -replace '## 9\.6 🎨 认知维度表征', '## 9.7 🎨 认知维度表征'
        $content = $content -replace '## 🎨 认知维度表征', '## 9.7 🎨 认知维度表征'
        $modified = $true
    }
    
    if ($content -match '## 🧠 认知维度表征' -and $content -notmatch '## 9\.7 🧠') {
        $content = $content -replace '## 9\.6 🧠 认知维度表征', '## 9.7 🧠 认知维度表征'
        $content = $content -replace '## 🧠 认知维度表征', '## 9.7 🧠 认知维度表征'
        $modified = $true
    }
    
    if ($content -match '## 👨‍🏫 专家观点与论证' -and $content -notmatch '## 9\.6 👨‍🏫') {
        $content = $content -replace '## 9\.4 👨‍🏫 专家观点与论证', '## 9.6 👨‍🏫 专家观点与论证'
        $content = $content -replace '## 👨‍🏫 专家观点与论证', '## 9.6 👨‍🏫 专家观点与论证'
        $modified = $true
    }
    
    if ($content -match '## 📚 习题库' -and $content -notmatch '## 9\.5 📚') {
        $content = $content -replace '## 9\.6 📚 习题库', '## 9.5 📚 习题库'
        $content = $content -replace '## 📚 习题库', '## 9.5 📚 习题库'
        $modified = $true
    }
    
    if ($content -match '## 🎓 学习路径' -and $content -notmatch '## 9\.4 🎓') {
        $content = $content -replace '## 9\.5 🎓 学习路径', '## 9.4 🎓 学习路径'
        $content = $content -replace '## 🎓 学习路径', '## 9.4 🎓 学习路径'
        $modified = $true
    }
    
    # 更新目录中的链接顺序
    if ($modified -or $content -match '9\.6 \[专家观点与论证\]' -and $content -match '9\.5 \[习题库\]') {
        # 检查目录中是否有错误的顺序
        if ($content -match '9\.5 \[习题库\]' -and $content -match '9\.6 \[专家观点与论证\]') {
            # 如果目录中9.5在9.6之前，顺序正确，但需要确保链接正确
            # 不需要修改
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
