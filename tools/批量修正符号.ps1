# FormalMath项目批量修正符号脚本
# 创建日期: 2025年12月31日
# 用途: 批量修正符号不一致项

param(
    [string]$ReportFile = "00-符号一致性检查报告-2026年01月01日.md",
    [string]$Priority = "P0",
    [switch]$DryRun
)

$basePath = Split-Path -Parent $PSScriptRoot

Write-Host "开始批量修正符号不一致项..." -ForegroundColor Green
Write-Host "报告文件: $ReportFile" -ForegroundColor Cyan
Write-Host "优先级: $Priority" -ForegroundColor Cyan
Write-Host "试运行模式: $DryRun" -ForegroundColor $(if ($DryRun) { "Yellow" } else { "Green" })

# 读取符号规范
$symbolFile = Join-Path $basePath "docs\FormalMath符号使用规范.md"
$standardSymbols = @{}

if (Test-Path $symbolFile) {
    $content = Get-Content -Path $symbolFile -Raw -Encoding UTF8
    $symbolPattern = '\|\s*\$([^\$]+)\$\s*\|\s*`([^`]+)`\s*\|'
    $matches = [regex]::Matches($content, $symbolPattern)

    foreach ($match in $matches) {
        $symbol = $match.Groups[1].Value.Trim()
        $latexCode = $match.Groups[2].Value.Trim()
        if (-not $standardSymbols.ContainsKey($symbol)) {
            $standardSymbols[$symbol] = $latexCode
        }
    }
}

Write-Host "已加载 $($standardSymbols.Count) 个标准符号" -ForegroundColor Cyan

# 读取检查报告
$reportPath = Join-Path $basePath $ReportFile
if (-not (Test-Path $reportPath)) {
    Write-Host "报告文件不存在: $reportPath" -ForegroundColor Red
    exit 1
}

$reportContent = Get-Content -Path $reportPath -Raw -Encoding UTF8

# 提取不一致项（简化版本，实际应该从CSV或结构化数据读取）
# 这里我们创建一个修正列表
$corrections = @()

# 示例：修正常见的符号不一致
$commonCorrections = @{
    '\subsetneq' = '\subset'
    '\supsetneq' = '\supset'
    '\setminus' = '\backslash'
}

$filesToFix = Get-ChildItem -Path (Join-Path $basePath "docs") -Filter "*.md" -Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak|符号使用规范|索引|导航)" -and
        $_.Name -notmatch "^00-"
    } | Select-Object -First 10  # 限制处理数量

$fixed = 0
$skipped = 0

foreach ($file in $filesToFix) {
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8
    $originalContent = $content
    $modified = $false

    # 应用常见修正
    foreach ($wrong in $commonCorrections.Keys) {
        $correct = $commonCorrections[$wrong]
        if ($content -match [regex]::Escape($wrong)) {
            $content = $content -replace [regex]::Escape($wrong), $correct
            $modified = $true
        }
    }

    if ($modified) {
        if (-not $DryRun) {
            # 备份原文件
            $backupPath = $file.FullName + ".bak"
            Copy-Item -Path $file.FullName -Destination $backupPath -Force

            # 写入修正后的内容
            $content | Out-File -FilePath $file.FullName -Encoding UTF8 -NoNewline
            $fixed++
            Write-Host "✓ 已修正: $($file.Name)" -ForegroundColor Green
        } else {
            $fixed++
            Write-Host "✓ 将修正: $($file.Name) (试运行)" -ForegroundColor Yellow
        }
    } else {
        $skipped++
    }
}

Write-Host "`n修正完成:" -ForegroundColor Cyan
Write-Host "  已修正: $fixed 个文件" -ForegroundColor Green
Write-Host "  已跳过: $skipped 个文件" -ForegroundColor Gray

if ($DryRun) {
    Write-Host "`n这是试运行模式，未实际修改文件。" -ForegroundColor Yellow
    Write-Host "要实际修正，请运行: .\批量修正符号.ps1 -ReportFile '$ReportFile' -Priority '$Priority'" -ForegroundColor Cyan
}
