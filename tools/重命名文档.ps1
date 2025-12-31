# FormalMath项目文档重命名脚本
# 创建日期: 2025年12月29日
# 用途: 统一根目录文档命名

$renameMap = @{
    '00-P1级项目质量提升完成报告-2025年12月11日.md' = '00-质量提升报告-2025年12月11日.md'
    '00-Week2规范建立完成报告-2025年12月29日.md' = '00-规范建立报告-2025年12月29日.md'
    '00-全面任务梳理与后续规划-2025年12月.md' = '00-任务规划-2025年12月.md'
    '00-文档清理执行报告-2025年12月29日.md' = '00-清理报告-2025年12月29日.md'
    '00-理解认知表征视角推进规划-2025年12月1日.md' = '00-认知表征规划-2025年12月1日.md'
    '00-第一阶段完成总结-2025年12月29日.md' = '00-第一阶段总结-2025年12月29日.md'
    '00-项目全面批判性评价与改进计划-2025年12月29日.md' = '00-评价报告-2025年12月29日.md'
    '00-项目后续推进总体规划-2025年12月1日.md' = '00-推进规划-2025年12月1日.md'
    '00-项目持续推进完成总结-2025年12月29日.md' = '00-项目总结-2025年12月29日.md'
    '00-项目改进执行计划-2025年12月29日.md' = '00-执行计划-2025年12月29日.md'
}

$renamed = 0
$notFound = 0

Write-Host "开始重命名文档..." -ForegroundColor Green

foreach ($oldName in $renameMap.Keys) {
    $newName = $renameMap[$oldName]
    if (Test-Path $oldName) {
        Rename-Item -Path $oldName -NewName $newName -Force
        $renamed++
        Write-Host "已重命名: $oldName -> $newName" -ForegroundColor Green
    } else {
        $notFound++
        Write-Host "未找到: $oldName" -ForegroundColor Yellow
    }
}

Write-Host "`n重命名完成:" -ForegroundColor Cyan
Write-Host "  成功重命名: $renamed 个文件" -ForegroundColor Green
Write-Host "  未找到文件: $notFound 个" -ForegroundColor Yellow
