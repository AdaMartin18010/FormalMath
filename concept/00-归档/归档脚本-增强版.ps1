# FormalMath项目归档脚本 - 增强版
# 创建日期: 2025年11月28日
# 说明: 分批归档文件，避免文件占用问题

Write-Host "开始归档工作..." -ForegroundColor Green

$baseDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$archiveDir = Join-Path $baseDir "00-归档"

# 确保归档目录存在
$dirs = @(
    "01-历史进度报告",
    "02-脚本文件",
    "03-view文件夹",
    "04-集合论范畴论视角",
    "05-辅助工具模块",
    "06-资源库"
)

foreach ($dir in $dirs) {
    $fullPath = Join-Path $archiveDir $dir
    if (-not (Test-Path $fullPath)) {
        New-Item -ItemType Directory -Path $fullPath -Force | Out-Null
    }
}

# 归档函数
function Archive-Files {
    param(
        [string[]]$Files,
        [string]$DestDir,
        [string]$Description
    )
    
    $moved = 0
    $failed = 0
    
    foreach ($file in $Files) {
        $fullPath = Join-Path $baseDir $file
        if (Test-Path $fullPath) {
            try {
                $destPath = Join-Path $DestDir $file
                if (-not (Test-Path $destPath)) {
                    Copy-Item $fullPath $destPath -Force
                    Start-Sleep -Milliseconds 200
                    Remove-Item $fullPath -Force -ErrorAction SilentlyContinue
                    $moved++
                } else {
                    Remove-Item $fullPath -Force -ErrorAction SilentlyContinue
                    $moved++
                }
            } catch {
                $failed++
                Write-Host "  失败: $file" -ForegroundColor Yellow
            }
        }
    }
    
    Write-Host "$Description : 成功 $moved 个, 失败 $failed 个" -ForegroundColor Cyan
    return $moved
}

# 1. P0P1改进相关文件
Write-Host "`n归档P0P1改进相关文件..." -ForegroundColor Yellow
$files = @(
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
    "00-P0P1改进进度报告-2025年11月.md"
)
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "P0P1改进相关"

# 2. P1任务相关文件
Write-Host "`n归档P1任务相关文件..." -ForegroundColor Yellow
$files = @(
    "00-P1-6习题库创建进度总结-2025年11月.md",
    "00-P1任务推进计划-2025年11月.md",
    "00-P1任务进度报告-2025年11月.md"
)
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "P1任务相关"

# 3. 三视角相关文件
Write-Host "`n归档三视角相关文件..." -ForegroundColor Yellow
$files = @(
    "00-三视角内容重组实施计划.md",
    "00-三视角内容重组框架.md",
    "00-三视角内容重组示例-集合.md",
    "00-三视角转换工作总结.md",
    "00-三视角转换进度跟踪.md"
)
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "三视角相关"

# 4. 工作进度相关文件
Write-Host "`n归档工作进度相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-工作*.md" -File | Where-Object { $_.Name -notmatch "项目当前状态|项目完成总结" } | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "工作进度相关"

# 5. 批量深化相关文件
Write-Host "`n归档批量深化相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-批量*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "批量深化相关"

# 6. 改进计划相关文件
Write-Host "`n归档改进计划相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-改进*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "改进计划相关"

# 7. 概念体系相关文件
Write-Host "`n归档概念体系相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-概念体系*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "概念体系相关"

# 8. 文件结构相关文件
Write-Host "`n归档文件结构相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-文件结构*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "文件结构相关"

# 9. 目录格式相关文件
Write-Host "`n归档目录格式相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-目录格式*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "目录格式相关"

# 10. 形式化相关文件
Write-Host "`n归档形式化相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-形式化*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "形式化相关"

# 11. 参考文献相关文件
Write-Host "`n归档参考文献相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-参考文献*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "参考文献相关"

# 12. 应用实例相关文件
Write-Host "`n归档应用实例相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-应用实例*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "应用实例相关"

# 13. 历史背景相关文件
Write-Host "`n归档历史背景相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-历史背景*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "历史背景相关"

# 14. concept文件夹相关文件
Write-Host "`n归档concept文件夹相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "concept文件夹*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "concept文件夹相关"

# 15. 最终完成总结文件
Write-Host "`n归档最终完成总结文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-最终完成*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "最终完成总结相关"

# 16. 项目相关文件（保留项目当前状态和项目完成总结）
Write-Host "`n归档项目相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-项目*.md" -File | Where-Object { $_.Name -notmatch "项目当前状态|项目完成总结" } | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "项目相关"

# 17. 知识结构相关文件
Write-Host "`n归档知识结构相关文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-知识结构*.md" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "知识结构相关"

# 18. 脚本文件
Write-Host "`n归档脚本文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "*.ps1" -File | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "02-脚本文件") -Description "脚本文件"

# 19. 集合论范畴论视角文档
Write-Host "`n归档集合论范畴论视角文档..." -ForegroundColor Yellow
$files = @(
    "00-集合论与范畴论视角的概念体系重构实施计划.md",
    "00-集合论与范畴论视角的概念体系重构框架.md",
    "00-集合论与范畴论视角整合分析.md",
    "00-集合论与范畴论视角应用示例-群.md",
    "00-集合论与范畴论视角-核心概念双视角索引.md",
    "00-集合论与范畴论视角与新框架整合指南-2025年1月.md",
    "00-集合论视角的概念层次结构分析.md",
    "00-范畴论视角的概念关系动态表征.md"
)
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "04-集合论范畴论视角") -Description "集合论范畴论视角"

# 20. 其他文件
Write-Host "`n归档其他文件..." -ForegroundColor Yellow
$files = Get-ChildItem -Path $baseDir -Filter "00-*.md" -File | Where-Object { 
    $_.Name -notmatch "(README|SUMMARY|归档|理论深化|项目当前状态|项目完成总结|P0P1|P1|三视角|工作|批量|改进|概念体系|文件结构|目录格式|形式化|参考文献|应用实例|历史背景|concept文件夹|最终完成|项目|知识结构|集合论|范畴论|对标|当前工作|内容深化|习题库|公理基础|内容增强|国际|多种思维|完整索引|实用模板|实际应用|常见问题|快速参考|快速导航|更新日志|系统概览|综合使用|网络论证|自我指涉|资源收集|跨模块|阶段|符号系统|文档目录|锚点|数学教育学|权威资源|核心概念与新框架|概念定义|目录清理)" 
} | ForEach-Object { $_.Name }
Archive-Files -Files $files -DestDir (Join-Path $archiveDir "01-历史进度报告") -Description "其他文件"

Write-Host "`n归档工作完成！" -ForegroundColor Green
Write-Host "请检查归档目录确认文件已成功归档。" -ForegroundColor Cyan

