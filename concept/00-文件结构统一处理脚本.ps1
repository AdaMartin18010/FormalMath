# 文件结构统一处理脚本
# 为所有核心概念文件添加统一的目录和编号

$conceptFiles = Get-ChildItem "g:\_src\FormalMath\concept\核心概念\*.md" | Sort-Object Name

foreach ($file in $conceptFiles) {
    Write-Host "处理文件: $($file.Name)"

    $content = Get-Content $file.FullName -Raw -Encoding UTF8

    # 检查是否已有目录
    if ($content -notmatch "## 📑 目录") {
        # 在概述之前插入目录
        $content = $content -replace "(?s)(---\s*\n\s*)(## 📋 概述)", "`$1## 📑 目录`n`n1. [概述](#1-概述)`n2. [严格定义](#2-严格定义)`n   - 2.1 [基础定义 (L0)](#21-基础定义-l0)`n   - 2.2 [形式化定义 (L1)](#22-形式化定义-l1)`n3. [历史背景](#3-历史背景)`n   - 3.1 [发展脉络](#31-发展脉络)`n   - 3.2 [关键人物](#32-关键人物)`n   - 3.3 [重要事件](#33-重要事件)`n4. [性质与定理](#4-性质与定理)`n   - 4.1 [基本性质 (L1)](#41-基本性质-l1)`n   - 4.2 [重要定理 (L2)](#42-重要定理-l2)`n5. [形式化证明](#5-形式化证明)（如果有）`n6. [应用实例](#6-应用实例)`n   - 6.1 [理论应用](#61-理论应用)`n   - 6.2 [实际应用](#62-实际应用)`n7. [关联概念](#7-关联概念)`n8. [参考文献](#8-参考文献)`n9. [其他部分](#9-其他部分)`n`n---`n`n`$2"
    }

    # 统一编号主要章节
    $content = $content -replace "## 📋 概述", "## 1. 📋 概述"
    $content = $content -replace "## 🎯 严格定义", "## 2. 🎯 严格定义"
    $content = $content -replace "## 📚 历史背景", "## 3. 📚 历史背景"
    $content = $content -replace "## 🔍 性质与定理", "## 4. 🔍 性质与定理"
    $content = $content -replace "## 🔬 形式化证明", "## 5. 🔬 形式化证明"
    $content = $content -replace "## 💡 应用实例", "## 6. 💡 应用实例"
    $content = $content -replace "## 🔗 关联概念", "## 7. 🔗 关联概念"
    $content = $content -replace "## 📖 参考文献", "## 8. 📖 参考文献"

    # 统一编号子章节
    $content = $content -replace "### 基础定义 \(L0\)", "### 2.1 基础定义 (L0)"
    $content = $content -replace "### 形式化定义 \(L1\)", "### 2.2 形式化定义 (L1)"
    $content = $content -replace "### 高级定义 \(L2\)", "### 2.3 高级定义 (L2)"

    $content = $content -replace "### 发展脉络", "### 3.1 发展脉络"
    $content = $content -replace "### 关键人物", "### 3.2 关键人物"
    $content = $content -replace "### 重要事件", "### 3.3 重要事件"

    $content = $content -replace "### 基本性质 \(L1\)", "### 4.1 基本性质 (L1)"
    $content = $content -replace "### 重要定理 \(L2\)", "### 4.2 重要定理 (L2)"

    $content = $content -replace "### 理论应用", "### 6.1 理论应用"
    $content = $content -replace "### 实际应用", "### 6.2 实际应用"

    # 保存文件
    Set-Content -Path $file.FullName -Value $content -Encoding UTF8 -NoNewline

    Write-Host "完成: $($file.Name)"
}

Write-Host "`n所有文件处理完成！"
