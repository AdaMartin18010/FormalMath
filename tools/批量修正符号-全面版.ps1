# FormalMath项目批量修正符号脚本（全面版）
# 创建日期: 2026年01月02日
# 用途: 批量修正所有符号不一致项

param(
    [int]$BatchSize = 500,
    [switch]$DryRun,
    [switch]$Backup
)

$basePath = Split-Path -Parent $PSScriptRoot
$fixedCount = 0
$skippedCount = 0
$processedFiles = @()

Write-Host "开始批量修正符号不一致项（全面版）..." -ForegroundColor Green
Write-Host "批次大小: $BatchSize" -ForegroundColor Cyan
Write-Host "试运行模式: $DryRun" -ForegroundColor $(if ($DryRun) { "Yellow" } else { "Green" })
Write-Host "备份模式: $Backup" -ForegroundColor Cyan

# 全面符号修正规则（按优先级排序）
$correctionRules = @(
    # 高优先级：常见错误
    @{ Pattern = '\\leqftrightarrow'; Replacement = '\leftrightarrow' },
    @{ Pattern = '\\leqft\('; Replacement = '\left(' },
    @{ Pattern = '\\leqft\{'; Replacement = '\left\{' },
    @{ Pattern = '\\leqft\['; Replacement = '\left[' },
    @{ Pattern = '\\leqft'; Replacement = '\left' },
    @{ Pattern = '\\geqq'; Replacement = '\geq' },
    @{ Pattern = '\\leqq'; Replacement = '\leq' },
    @{ Pattern = '\\\\leftrightarrow'; Replacement = '\leftrightarrow' },
    @{ Pattern = '\\\\leftarrow'; Replacement = '\leftarrow' },
    @{ Pattern = '\\\\rightarrow'; Replacement = '\rightarrow' },
    @{ Pattern = '\\\\leq'; Replacement = '\leq' },
    @{ Pattern = '\\\\geq'; Replacement = '\geq' },
    @{ Pattern = '\\\\left\('; Replacement = '\left(' },
    @{ Pattern = '\\\\left\{'; Replacement = '\left\{' },
    @{ Pattern = '\\\\left\['; Replacement = '\left[' },
    # 否定符号错误
    @{ Pattern = '\\neqqqqqqq'; Replacement = '\neq' },
    @{ Pattern = '\\neqqqqqqg'; Replacement = '\neg' },
    @{ Pattern = '\\neqqqqqq'; Replacement = '\neq' },
    @{ Pattern = '\\neqqqqq'; Replacement = '\neq' },
    @{ Pattern = '\\neqqqq'; Replacement = '\neq' },
    @{ Pattern = '\\neqqqg'; Replacement = '\neg' },
    @{ Pattern = '\\neqqq'; Replacement = '\neq' },
    @{ Pattern = '\\neqq'; Replacement = '\neq' },
    @{ Pattern = '\\neqxists'; Replacement = '\nexists' },
    # 基础符号
    @{ Pattern = '\\ne'; Replacement = '\neq' },
    @{ Pattern = '\\le'; Replacement = '\leq' },
    @{ Pattern = '\\ge'; Replacement = '\geq' }
)

# 获取所有需要处理的文件
$allFiles = Get-ChildItem -Path $basePath -Filter "*.md" -Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak)" -and
        $_.FullName -notmatch "00-.*\.md$"
    }

Write-Host "找到 $($allFiles.Count) 个文件需要检查" -ForegroundColor Cyan

# 批量处理文件
$batch = 0
foreach ($file in $allFiles) {
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8 -ErrorAction SilentlyContinue
    if (-not $content) {
        $skippedCount++
        continue
    }

    $originalContent = $content
    $modified = $false
    $changes = @()

    # 应用修正规则
    foreach ($rule in $correctionRules) {
        $pattern = $rule.Pattern
        $replacement = $rule.Replacement
        $escapedPattern = [regex]::Escape($pattern)
        
        if ($content -match $escapedPattern) {
            $count = ([regex]::Matches($content, $escapedPattern)).Count
            $content = $content -replace $escapedPattern, $replacement
            $changes += "$pattern -> $replacement ($count 处)"
            $modified = $true
        }
    }

    if ($modified) {
        if (-not $DryRun) {
            if ($Backup) {
                $backupPath = $file.FullName + ".bak"
                Copy-Item -Path $file.FullName -Destination $backupPath -Force
            }
            $content | Out-File -FilePath $file.FullName -Encoding UTF8 -NoNewline
        }

        $relativePath = $file.FullName.Replace($basePath, "").TrimStart('\').Replace('\', '/')
        $processedFiles += [PSCustomObject]@{
            File = $relativePath
            Changes = $changes -join "; "
        }
        $fixedCount++

        if ($fixedCount % 100 -eq 0) {
            Write-Host "已处理 $fixedCount 个文件..." -ForegroundColor Yellow
        }
    } else {
        $skippedCount++
    }
}

Write-Host "`n修正完成:" -ForegroundColor Cyan
Write-Host "  已修正: $fixedCount 个文件" -ForegroundColor Green
Write-Host "  已跳过: $skippedCount 个文件" -ForegroundColor Gray

if ($DryRun) {
    Write-Host "`n这是试运行模式，未实际修改文件。" -ForegroundColor Yellow
    Write-Host "要实际修正，请运行: .\批量修正符号-全面版.ps1 -Backup" -ForegroundColor Cyan
} else {
    Write-Host "`n修正详情已记录到变量 `$processedFiles" -ForegroundColor Cyan
}

return $processedFiles
