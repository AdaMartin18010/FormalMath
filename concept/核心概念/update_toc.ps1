# 批量更新核心概念文件的目录，添加5.4、5.5、5.6的链接

$files = @(
    "03-自然数-三视角版.md",
    "04-整数-三视角版.md",
    "05-有理数-三视角版.md",
    "06-实数-三视角版.md",
    "07-复数-三视角版.md",
    "08-群-三视角版.md",
    "09-环-三视角版.md",
    "13-极限-三视角版.md",
    "14-连续-三视角版.md",
    "15-导数-三视角版.md",
    "16-积分-三视角版.md",
    "18-流形-三视角版.md",
    "19-黎曼流形-三视角版.md",
    "20-曲率-三视角版.md",
    "21-概形-三视角版.md",
    "22-层-三视角版.md",
    "23-拓扑空间-三视角版.md",
    "24-同伦-三视角版.md",
    "25-同调-三视角版.md",
    "26-素数-三视角版.md",
    "27-同余-三视角版.md",
    "28-L函数-三视角版.md",
    "29-图-三视角版.md",
    "30-组合数-三视角版.md",
    "31-算法-三视角版.md",
    "32-表示-三视角版.md",
    "33-朗兰兹纲领-三视角版.md"
)

$conceptNames = @{
    "03-自然数-三视角版.md" = "自然数"
    "04-整数-三视角版.md" = "整数"
    "05-有理数-三视角版.md" = "有理数"
    "06-实数-三视角版.md" = "实数"
    "07-复数-三视角版.md" = "复数"
    "08-群-三视角版.md" = "群"
    "09-环-三视角版.md" = "环"
    "13-极限-三视角版.md" = "极限"
    "14-连续-三视角版.md" = "连续"
    "15-导数-三视角版.md" = "导数"
    "16-积分-三视角版.md" = "积分"
    "18-流形-三视角版.md" = "流形"
    "19-黎曼流形-三视角版.md" = "黎曼流形"
    "20-曲率-三视角版.md" = "曲率"
    "21-概形-三视角版.md" = "概形"
    "22-层-三视角版.md" = "层"
    "23-拓扑空间-三视角版.md" = "拓扑空间"
    "24-同伦-三视角版.md" = "同伦"
    "25-同调-三视角版.md" = "同调"
    "26-素数-三视角版.md" = "素数"
    "27-同余-三视角版.md" = "同余"
    "28-L函数-三视角版.md" = "L函数"
    "29-图-三视角版.md" = "图"
    "30-组合数-三视角版.md" = "组合数"
    "31-算法-三视角版.md" = "算法"
    "32-表示-三视角版.md" = "表示"
    "33-朗兰兹纲领-三视角版.md" = "朗兰兹纲领"
}

$updated = 0
$skipped = 0

foreach ($file in $files) {
    if (Test-Path $file) {
        $content = Get-Content $file -Raw -Encoding UTF8
        $conceptName = $conceptNames[$file]
        
        # 检查是否已经包含5.4链接
        if ($content -match "- \[5\.4 决策树") {
            Write-Host "跳过: $file (已包含5.4链接)" -ForegroundColor Yellow
            $skipped++
            continue
        }
        
        # 查找5.3的位置并添加5.4、5.5、5.6
        $pattern = "(- \[5\.3 多视角表征：从不同角度表征$conceptName\]\(#53-多视角表征从不同角度表征$conceptName\))\s*\r?\n"
        $replacement = "`$1`r`n      - [5.4 决策树：$conceptName问题分类和策略选择](#54-决策树$conceptName问题分类和策略选择)`r`n      - [5.5 决策逻辑路径：$conceptName问题解决过程](#55-决策逻辑路径$conceptName问题解决过程)`r`n      - [5.6 多维对比矩阵：$conceptName概念特征对比](#56-多维对比矩阵$conceptName概念特征对比)`r`n"
        
        if ($content -match $pattern) {
            $newContent = $content -replace $pattern, $replacement
            Set-Content $file -Value $newContent -Encoding UTF8 -NoNewline
            Write-Host "更新: $file" -ForegroundColor Green
            $updated++
        } else {
            Write-Host "未找到模式: $file" -ForegroundColor Red
        }
    } else {
        Write-Host "文件不存在: $file" -ForegroundColor Red
    }
}

Write-Host "`n=== 更新完成 ===" -ForegroundColor Cyan
Write-Host "更新: $updated 个文件"
Write-Host "跳过: $skipped 个文件"

