# FormalMath项目创建README模板脚本
# 创建日期: 2025年12月31日
# 用途: 为各子目录创建00-README.md模板

$basePath = Split-Path -Parent $PSScriptRoot
$docsPath = Join-Path $basePath "docs"

Write-Host "开始创建README模板..." -ForegroundColor Green

# 定义各分支的说明
$branchDescriptions = @{
    "00-核心概念理解三问" = "核心概念理解框架，提供理解三问模板和知识图谱系统"
    "01-基础数学" = "集合论、数系、序关系等基础数学内容"
    "02-代数结构" = "群论、环论、域论、模论等代数结构理论"
    "03-分析学" = "实分析、复分析、泛函分析等分析学内容"
    "04-几何学" = "欧几里得几何、非欧几何、射影几何等"
    "05-拓扑学" = "点集拓扑、代数拓扑、微分拓扑等"
    "06-数论" = "初等数论、代数数论、解析数论等"
    "07-逻辑学" = "数理逻辑、形式逻辑、模型论等"
    "08-计算数学" = "数值计算、算法、计算复杂性等"
    "09-形式化证明" = "形式化证明系统、定理证明器等"
    "10-语义模型" = "语义模型、形式化语义、类型论等"
    "11-高级数学" = "高级数学内容和前沿理论"
    "12-应用数学" = "应用数学、数学建模等"
    "13-代数几何" = "代数几何理论和应用"
    "14-微分几何" = "微分几何理论和应用"
    "15-同调代数" = "同调代数理论和应用"
    "99-归档文档" = "归档的历史文档和旧版本"
}

$created = 0
$skipped = 0

foreach ($branch in $branchDescriptions.Keys) {
    $readmePath = Join-Path $docsPath "$branch\00-README.md"

    if (Test-Path $readmePath) {
        $skipped++
        Write-Host "已存在: $readmePath" -ForegroundColor Yellow
        continue
    }

    $branchDir = Join-Path $docsPath $branch
    if (-not (Test-Path $branchDir)) {
        Write-Host "目录不存在: $branchDir" -ForegroundColor Red
        continue
    }

    $description = $branchDescriptions[$branch]
    $readmeContent = @"
# $($branch -replace '^\d{2}-', '')

**最后更新**: 2025年12月31日

---

## 📋 目录概述

$description

---

## 📁 目录结构

查看本目录下的文档和子目录。

---

## 📚 相关文档

- [项目索引](../项目索引.md) - 完整的项目文档索引
- [文档格式规范](../FormalMath文档格式规范-2025年12月.md) - 文档格式规范

---

**最后更新**: 2025年12月31日
"@

    try {
        $readmeContent | Out-File -FilePath $readmePath -Encoding UTF8 -Force
        $created++
        Write-Host "✓ 已创建: $readmePath" -ForegroundColor Green
    } catch {
        Write-Host "✗ 错误: $readmePath" -ForegroundColor Red
        Write-Host "  错误信息: $_" -ForegroundColor Red
    }
}

Write-Host "`n创建完成:" -ForegroundColor Cyan
Write-Host "  已创建: $created 个文件" -ForegroundColor Green
Write-Host "  已跳过: $skipped 个文件" -ForegroundColor Yellow
