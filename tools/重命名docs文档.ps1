# FormalMath项目docs目录文档重命名脚本
# 创建日期: 2025年12月31日
# 用途: 统一docs目录文档命名

$basePath = Split-Path -Parent $PSScriptRoot
$docsPath = Join-Path $basePath "docs"

Write-Host "开始重命名docs目录文档..." -ForegroundColor Green
Write-Host "基础路径: $basePath" -ForegroundColor Cyan

$renameMap = @{
    # 00-核心概念理解三问目录
    '00-核心概念理解三问\00-理解三问模板与框架.md' = '00-核心概念理解三问\00-README.md'
    '00-核心概念理解三问\00-跨领域类比图谱.md' = '00-核心概念理解三问\01-跨领域类比图谱.md'

    # 00-核心概念理解三问\11-核心定理多表征目录
    '00-核心概念理解三问\11-核心定理多表征\00-多表征框架.md' = '00-核心概念理解三问\11-核心定理多表征\00-README.md'

    # 00-核心概念理解三问\12-知识图谱系统目录
    '00-核心概念理解三问\12-知识图谱系统\00-知识图谱总体框架.md' = '00-核心概念理解三问\12-知识图谱系统\00-README.md'

    # 01-基础数学\序关系论证体系目录
    '01-基础数学\序关系论证体系\00-序关系论证体系总结-国际标准版.md' = '01-基础数学\序关系论证体系\00-总结报告-国际标准版.md'

    # 01-基础数学\抽象代数结构论证目录
    '01-基础数学\抽象代数结构论证\00-抽象代数结构论证总结-国际标准版.md' = '01-基础数学\抽象代数结构论证\00-总结报告-国际标准版.md'

    # 02-代数结构\00-项目总览目录
    '02-代数结构\00-项目总览\00-代数结构README.md' = '02-代数结构\00-项目总览\README.md'
    '02-代数结构\00-项目总览\00-代数结构文档索引.md' = '02-代数结构\00-项目总览\00-文档索引.md'
    '02-代数结构\00-项目总览\00-代数结构项目总览.md' = '02-代数结构\00-项目总览\00-项目总览.md'

    # 02-代数结构\01-理论基础目录
    '02-代数结构\01-理论基础\00-ZFC到抽象代数结构完整论证-国际标准版.md' = '02-代数结构\01-理论基础\01-ZFC到抽象代数结构完整论证-国际标准版.md'
    '02-代数结构\01-理论基础\00-代数结构论证体系总结-国际标准版.md' = '02-代数结构\01-理论基础\00-总结报告-国际标准版.md'

    # 02-代数结构\06-技术实现参考\Python实现目录
    '02-代数结构\06-技术实现参考\Python实现\00-Python实现-代数结构综合工具.md' = '02-代数结构\06-技术实现参考\Python实现\01-Python实现-代数结构综合工具.md'

    # 02-代数结构\99-归档文档\Python实现相关文档目录
    '02-代数结构\99-归档文档\Python实现相关文档\00-Python实现-代数结构教学资源指南.md' = '02-代数结构\99-归档文档\Python实现相关文档\01-Python实现-代数结构教学资源指南.md'
}

$renamed = 0
$notFound = 0
$errors = 0

foreach ($oldPath in $renameMap.Keys) {
    $newPath = $renameMap[$oldPath]
    $fullOldPath = Join-Path $docsPath $oldPath
    $fullNewPath = Join-Path $docsPath $newPath

    if (Test-Path $fullOldPath) {
        try {
            # 确保目标目录存在
            $newDir = Split-Path -Parent $fullNewPath
            if (-not (Test-Path $newDir)) {
                New-Item -ItemType Directory -Path $newDir -Force | Out-Null
            }

            Rename-Item -Path $fullOldPath -NewName (Split-Path -Leaf $newPath) -Force
            $renamed++
            Write-Host "✓ 已重命名: $oldPath -> $newPath" -ForegroundColor Green
        } catch {
            $errors++
            Write-Host "✗ 错误: $oldPath -> $newPath" -ForegroundColor Red
            Write-Host "  错误信息: $_" -ForegroundColor Red
        }
    } else {
        $notFound++
        Write-Host "⚠ 未找到: $oldPath" -ForegroundColor Yellow
    }
}

Write-Host "`n重命名完成:" -ForegroundColor Cyan
Write-Host "  成功重命名: $renamed 个文件" -ForegroundColor Green
Write-Host "  未找到文件: $notFound 个" -ForegroundColor Yellow
Write-Host "  错误: $errors 个" -ForegroundColor Red
