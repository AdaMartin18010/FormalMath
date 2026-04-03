# MSC编码修正脚本
# 执行格式统一和编码错误修正

$stats = @{
    totalFiles = 0
    mscFiles = 0
    xxToXX = 0
    code28to26 = 0  # 实分析相关
    code28to30 = 0  # 复分析相关
    code28to46 = 0  # 泛函分析相关
    addedMsc = 0
}

# 1. 统计当前情况
Write-Host "=== 开始统计当前MSC编码情况 ===" -ForegroundColor Green
$allFiles = Get-ChildItem -Path "e:\_src\FormalMath" -Recurse -Filter "*.md"
$stats.totalFiles = $allFiles.Count

foreach($file in $allFiles) {
    if(Select-String -Path $file.FullName -Pattern "^msc_primary:" -Quiet) {
        $stats.mscFiles++
    }
}

Write-Host "总文档数: $($stats.totalFiles)" -ForegroundColor Cyan
Write-Host "已标注MSC文档: $($stats.mscFiles)" -ForegroundColor Cyan
Write-Host "当前覆盖率: $([math]::Round(($stats.mscFiles/$stats.totalFiles)*100, 2))%" -ForegroundColor Cyan

# 2. 格式修正：xx → XX
Write-Host "`n=== 执行格式修正：小写xx → 大写XX ===" -ForegroundColor Green
$filesWithXX = Get-ChildItem -Path "e:\_src\FormalMath\docs" -Recurse -Filter "*.md" | 
    Where-Object { Select-String -Path $_.FullName -Pattern "\d{2}-xx\b" -Quiet }

foreach($file in $filesWithXX) {
    $content = Get-Content $file.FullName -Raw
    $originalContent = $content
    # 匹配数字-小写xx的模式，替换为数字-大写XX
    $content = $content -replace '(\d{2})-xx\b', '$1-XX'
    if($content -ne $originalContent) {
        Set-Content -Path $file.FullName -Value $content -NoNewline
        $matches = ([regex]::Matches($originalContent, '\d{2}-xx\b')).Count
        $stats.xxToXX += $matches
        Write-Host "  修正: $($file.Name) ($matches 处)" -ForegroundColor DarkGray
    }
}

# 3. 编码错误修正
Write-Host "`n=== 执行编码错误修正 ===" -ForegroundColor Green

# 获取所有带MSC编码的分析学文档
$analysisFiles = Get-ChildItem -Path "e:\_src\FormalMath\docs\03-分析学" -Recurse -Filter "*.md"

foreach($file in $analysisFiles) {
    $content = Get-Content $file.FullName -Raw
    $originalContent = $content
    
    # 分析学文档中28-XX→26-XX（实分析/实函数）
    if($content -match "28-XX") {
        # 检查文件内容判断类型
        $fileContentLower = $content.ToLower()
        
        # 复分析关键词
        $isComplex = $fileContentLower -match "复分析|复变|解析函数|全纯|柯西-黎曼|complex analysis|holomorphic|analytic function"
        # 泛函分析关键词
        $isFunctional = $fileContentLower -match "泛函|函数空间|算子|functional|operator|banach|hilbert"
        # 实分析关键词
        $isReal = $fileContentLower -match "实分析|实变|测度|积分|勒贝格|measure|integration|lebesgue|real analysis"
        
        if($isComplex -and !$isReal) {
            # 复分析 → 30-XX
            $content = $content -replace "28-XX", "30-XX"
            $stats.code28to30++
            Write-Host "  28-XX→30-XX: $($file.Name) (复分析)" -ForegroundColor Yellow
        } elseif($isFunctional -and !$isReal) {
            # 泛函分析 → 46-XX
            $content = $content -replace "28-XX", "46-XX"
            $stats.code28to46++
            Write-Host "  28-XX→46-XX: $($file.Name) (泛函分析)" -ForegroundColor Yellow
        } else {
            # 默认实分析 → 26-XX
            $content = $content -replace "28-XX", "26-XX"
            $stats.code28to26++
            Write-Host "  28-XX→26-XX: $($file.Name) (实分析)" -ForegroundColor Yellow
        }
    }
    
    if($content -ne $originalContent) {
        Set-Content -Path $file.FullName -Value $content -NoNewline
    }
}

# 输出统计
Write-Host "`n=== 修正完成统计 ===" -ForegroundColor Green
Write-Host "格式修正 (xx→XX): $($stats.xxToXX) 处" -ForegroundColor Cyan
Write-Host "28-XX→26-XX (实分析): $($stats.code28to26) 处" -ForegroundColor Cyan
Write-Host "28-XX→30-XX (复分析): $($stats.code28to30) 处" -ForegroundColor Cyan
Write-Host "28-XX→46-XX (泛函分析): $($stats.code28to46) 处" -ForegroundColor Cyan

# 导出统计结果
$stats | Export-Clixml "e:\_src\FormalMath\project\msc_fix_stats.xml"
Write-Host "`n统计结果已保存到: project\msc_fix_stats.xml" -ForegroundColor Green
