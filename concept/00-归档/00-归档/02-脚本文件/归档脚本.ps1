# 归档脚本
# 用途：将concept目录下与当前核心工作无关的文件归档到00-归档目录
# 创建日期：2025年11月28日

# 设置错误处理
$ErrorActionPreference = "Continue"

# 定义归档目录
$archiveRoot = "concept\00-归档"
$archiveReports = "$archiveRoot\01-历史进度报告"
$archiveScripts = "$archiveRoot\02-脚本文件"
$archiveView = "$archiveRoot\03-view文件夹"
$archiveSetCat = "$archiveRoot\04-集合论范畴论视角"
$archiveTools = "$archiveRoot\05-辅助工具模块"
$archiveResources = "$archiveRoot\06-资源库"

# 确保归档目录存在
New-Item -ItemType Directory -Force -Path $archiveReports | Out-Null
New-Item -ItemType Directory -Force -Path $archiveScripts | Out-Null
New-Item -ItemType Directory -Force -Path $archiveView | Out-Null
New-Item -ItemType Directory -Force -Path $archiveSetCat | Out-Null
New-Item -ItemType Directory -Force -Path $archiveTools | Out-Null
New-Item -ItemType Directory -Force -Path $archiveResources | Out-Null

Write-Host "开始归档文件..." -ForegroundColor Green

# 归档历史进度报告
Write-Host "归档历史进度报告..." -ForegroundColor Yellow
$reportFiles = @(
    "00-P0P1改进最终总结-2025年11月.md",
    "00-P0P1改进完成总结-2025年11月.md",
    "00-P0P1改进工作最新进度-2025年11月.md",
    "00-P0P1改进工作最终完成报告-2025年11月-最终版.md",
    "00-P0P1改进工作最终完成报告-2025年11月-完整版.md",
    "00-P0P1改进工作最终完成报告-2025年11月.md",
    "00-P0P1改进工作最终完成报告-最终版-2025年11月.md",
    "00-P0P1改进工作最终完成报告-完整版-2025年11月.md",
    "00-P0P1改进工作完成报告-2025年11月.md",
    "00-P0P1改进工作持续推进报告-2025年11月.md",
    "00-P0P1改进工作里程碑报告-2025年11月.md",
    "00-P0P1改进进度报告-2025年11月.md",
    "00-P1-6习题库创建进度总结-2025年11月.md",
    "00-P1任务推进计划-2025年11月.md",
    "00-P1任务进度报告-2025年11月.md",
    "00-三视角内容重组实施计划.md",
    "00-三视角内容重组框架.md",
    "00-三视角内容重组示例-集合.md",
    "00-三视角转换工作总结.md",
    "00-三视角转换进度跟踪.md",
    "00-工作完成总结-2025年11月28日.md",
    "00-工作完成总结-元认知分析-2025年11月28日.md",
    "00-工作进度-元认知分析-2025年11月28日.md",
    "00-工作进度-元认知分析-批量处理-2025年11月28日.md",
    "00-工作进度-数学家视角深化-2025年11月28日.md",
    "00-工作进度总结-2025年11月28日.md",
    "00-工作进度总结-最终版-2025年11月28日.md",
    "00-工作进度更新-元认知分析-2025年11月28日.md",
    "00-工作进度更新-数学家视角-2025年11月28日.md",
    "00-批量处理说明-数学家视角-2025年11月28日.md",
    "00-批量深化完成报告-2025年11月28日.md",
    "00-批量深化总结-2025年11月28日.md",
    "00-批量深化策略-2025年11月28日.md",
    "00-批量深化策略-高效版-2025年11月28日.md",
    "00-批量深化进度-2025年11月28日.md",
    "00-改进实施计划-P0P1优先级-2025年11月.md",
    "00-改进计划全面完成总结-2025年1月.md",
    "00-改进计划实施进度跟踪-2025年1月.md",
    "00-改进计划当前阶段完成报告-2025年1月.md",
    "00-改进计划阶段性完成总结-2025年1月.md",
    "00-概念体系全面完成最终报告-2025年1月.md",
    "00-概念体系全面完成总结-2025年1月.md",
    "00-概念体系全面梳理与推进工作总结-2025年1月.md",
    "00-概念体系全面梳理与推进计划-2025年1月.md",
    "00-概念体系最终完成报告-2025年1月.md",
    "00-概念体系持续推进最新总结-2025年1月.md",
    "00-概念体系持续推进总结-2025年1月.md",
    "00-概念体系深度改进计划-2025年1月.md",
    "00-文件结构统一最终完成报告-2025年11月-完整版.md",
    "00-文件结构统一最终完成报告-2025年11月.md",
    "00-文件结构统一完成报告-2025年11月.md",
    "00-文件结构统一模板-2025年11月.md",
    "00-目录格式修复完成报告-2025年11月.md",
    "00-目录格式统一完成报告-2025年11月.md",
    "00-形式化定义标准模板-2025年11月.md",
    "00-形式化定义检查清单-2025年11月.md",
    "00-形式化证明系统-2025年11月.md",
    "00-形式化证明补充最终报告-2025年11月.md",
    "00-形式化证明补充完成报告-2025年11月.md",
    "00-形式化证明补充进度-2025年11月.md",
    "00-历史背景补充模板-2025年11月.md",
    "00-参考文献补充批量处理-2025年11月.md",
    "00-参考文献补充模板-2025年11月.md",
    "00-参考文献补充进度总结-2025年11月.md",
    "00-应用实例补充检查清单-2025年11月.md",
    "00-应用实例补充模板-2025年11月.md",
    "concept文件夹100%完成总结-2025年1月.md",
    "concept文件夹全面完成报告-2025年1月.md",
    "concept文件夹全面推进计划-2025年1月.md",
    "concept文件夹最终完成确认-2025年1月.md",
    "concept文件夹完成确认-2025年11月-最终版.md",
    "concept文件夹持续推进总结-2025年1月.md",
    "concept文件夹推进进度报告-2025年1月.md",
    "concept文件夹核心工作完成总结-2025年1月.md",
    "00-最终完成总结-2025年11月28日.md",
    "00-最终完成总结-全部任务-2025年11月28日.md",
    "00-最终完成总结-全部工作-2025年11月28日.md",
    "00-项目全面批判性评价与改进计划-2025年11月.md",
    "00-项目完成总结.md",
    "00-知识结构总览.md",
    "00-知识结构重组全面完成总结.md",
    "00-知识结构重组最终总结.md",
    "00-知识结构重组完成总结.md",
    "00-知识结构重组方案.md",
    "00-习题库总览-2025年11月.md",
    "00-公理基础明确-2025年11月.md",
    "00-内容增强指南.md",
    "00-内容深化改进方案-2025年11月28日.md",
    "00-国际主流数学认知理论整合框架-2025年1月.md",
    "00-国际标准对齐总结-2025年11月.md",
    "00-多种思维表征方式对比与整合-2025年1月.md",
    "00-完整索引.md",
    "00-实用模板与清单.md",
    "00-实际应用案例.md",
    "00-对标分析与改进计划-2025年11月28日.md",
    "00-对标分析快速参考-2025年11月28日.md",
    "00-常见问题解答.md",
    "00-当前工作状态-2025年11月28日.md",
    "00-快速参考卡片.md",
    "00-快速导航.md",
    "00-数学教育学资源收集框架-2025年1月.md",
    "00-文档目录编号全面梳理报告-2025年1月.md",
    "00-更新日志.md",
    "00-权威资源对标改进计划.md",
    "00-权威资源对齐说明.md",
    "00-权威资源调研报告-2025年1月.md",
    "00-核心概念与新框架整合指南-2025年1月.md",
    "00-概念定义属性关系形式化论证证明系统-2025年1月.md",
    "00-符号系统规范-2025年11月.md",
    "00-系统概览.md",
    "00-综合使用指南.md",
    "00-网络论证对标研究报告.md",
    "00-自我指涉性理论.md",
    "00-资源收集进展总结报告-2025年1月.md",
    "00-跨模块整合指南.md",
    "00-阶段2-概念层次重构准备文档.md"
)

$movedReports = 0
foreach ($file in $reportFiles) {
    $source = "concept\$file"
    if (Test-Path $source) {
        try {
            Move-Item $source "$archiveReports\$file" -Force -ErrorAction Stop
            $movedReports++
        } catch {
            Write-Host "无法移动: $file - $($_.Exception.Message)" -ForegroundColor Red
        }
    }
}
Write-Host "已归档 $movedReports 个历史进度报告文件" -ForegroundColor Green

# 归档脚本文件
Write-Host "归档脚本文件..." -ForegroundColor Yellow
$scriptFiles = Get-ChildItem -Path "concept" -Filter "*.ps1" -File
$movedScripts = 0
foreach ($file in $scriptFiles) {
    try {
        Move-Item $file.FullName "$archiveScripts\$($file.Name)" -Force -ErrorAction Stop
        $movedScripts++
    } catch {
        Write-Host "无法移动: $($file.Name) - $($_.Exception.Message)" -ForegroundColor Red
    }
}
Write-Host "已归档 $movedScripts 个脚本文件" -ForegroundColor Green

# 归档view文件夹
Write-Host "归档view文件夹..." -ForegroundColor Yellow
if (Test-Path "concept\view") {
    try {
        robocopy "concept\view" "$archiveView\view" /E /MOVE /NFL /NDL /NJH /NJS /R:3 /W:1
        Write-Host "view文件夹已归档" -ForegroundColor Green
    } catch {
        Write-Host "无法归档view文件夹: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# 归档集合论和范畴论视角
Write-Host "归档集合论和范畴论视角..." -ForegroundColor Yellow
if (Test-Path "concept\00-集合论视角-核心概念分析") {
    try {
        robocopy "concept\00-集合论视角-核心概念分析" "$archiveSetCat\00-集合论视角-核心概念分析" /E /MOVE /NFL /NDL /NJH /NJS /R:3 /W:1
        Write-Host "集合论视角文件夹已归档" -ForegroundColor Green
    } catch {
        Write-Host "无法归档集合论视角文件夹: $($_.Exception.Message)" -ForegroundColor Red
    }
}

if (Test-Path "concept\00-范畴论视角-核心概念分析") {
    try {
        robocopy "concept\00-范畴论视角-核心概念分析" "$archiveSetCat\00-范畴论视角-核心概念分析" /E /MOVE /NFL /NDL /NJH /NJS /R:3 /W:1
        Write-Host "范畴论视角文件夹已归档" -ForegroundColor Green
    } catch {
        Write-Host "无法归档范畴论视角文件夹: $($_.Exception.Message)" -ForegroundColor Red
    }
}

$setCatFiles = @(
    "00-集合论与范畴论视角的概念体系重构实施计划.md",
    "00-集合论与范畴论视角的概念体系重构框架.md",
    "00-集合论与范畴论视角整合分析.md",
    "00-集合论与范畴论视角应用示例-群.md",
    "00-集合论与范畴论视角-核心概念双视角索引.md",
    "00-集合论与范畴论视角与新框架整合指南-2025年1月.md",
    "00-集合论视角的概念层次结构分析.md",
    "00-范畴论视角的概念关系动态表征.md"
)

$movedSetCat = 0
foreach ($file in $setCatFiles) {
    $source = "concept\$file"
    if (Test-Path $source) {
        try {
            Move-Item $source "$archiveSetCat\$file" -Force -ErrorAction Stop
            $movedSetCat++
        } catch {
            Write-Host "无法移动: $file - $($_.Exception.Message)" -ForegroundColor Red
        }
    }
}
Write-Host "已归档 $movedSetCat 个集合论范畴论视角文档" -ForegroundColor Green

# 归档辅助工具模块
Write-Host "归档辅助工具模块..." -ForegroundColor Yellow
$toolDirs = @("01-总体思维导图", "02-知识矩阵", "03-主题概念梳理", "04-认知工具", "05-知识关联网络", "06-文档主题分析")
$movedTools = 0
foreach ($dir in $toolDirs) {
    if (Test-Path "concept\$dir") {
        try {
            robocopy "concept\$dir" "$archiveTools\$dir" /E /MOVE /NFL /NDL /NJH /NJS /R:3 /W:1
            $movedTools++
        } catch {
            Write-Host "无法归档: $dir - $($_.Exception.Message)" -ForegroundColor Red
        }
    }
}
Write-Host "已归档 $movedTools 个辅助工具模块文件夹" -ForegroundColor Green

# 归档资源库
Write-Host "归档资源库..." -ForegroundColor Yellow
if (Test-Path "concept\00-资源库") {
    try {
        robocopy "concept\00-资源库" "$archiveResources\00-资源库" /E /MOVE /NFL /NDL /NJH /NJS /R:3 /W:1
        Write-Host "资源库文件夹已归档" -ForegroundColor Green
    } catch {
        Write-Host "无法归档资源库文件夹: $($_.Exception.Message)" -ForegroundColor Red
    }
}

Write-Host "`n归档完成！" -ForegroundColor Green
Write-Host "已归档文件统计:" -ForegroundColor Cyan
Write-Host "  - 历史进度报告: $movedReports 个文件" -ForegroundColor Cyan
Write-Host "  - 脚本文件: $movedScripts 个文件" -ForegroundColor Cyan
Write-Host "  - 集合论范畴论视角文档: $movedSetCat 个文件" -ForegroundColor Cyan
Write-Host "  - 辅助工具模块: $movedTools 个文件夹" -ForegroundColor Cyan
