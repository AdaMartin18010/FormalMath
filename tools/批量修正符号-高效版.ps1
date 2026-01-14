# FormalMath项目批量修正符号脚本（高效版）
# 创建日期: 2026年01月02日
# 用途: 批量修正符号不一致项，高效处理大量文件

param(
    [int]$BatchSize = 200,
    [switch]$DryRun,
    [switch]$Backup
)

$basePath = Split-Path -Parent $PSScriptRoot
$fixedCount = 0
$skippedCount = 0
$processedFiles = @()

Write-Host "开始批量修正符号不一致项..." -ForegroundColor Green
Write-Host "批次大小: $BatchSize" -ForegroundColor Cyan
Write-Host "试运行模式: $DryRun" -ForegroundColor $(if ($DryRun) { "Yellow" } else { "Green" })
Write-Host "备份模式: $Backup" -ForegroundColor Cyan

# 常见符号修正规则
$correctionRules = @{
    '\ne' = '\neq'
    '\le' = '\leq'
    '\ge' = '\geq'
}

# 获取所有需要处理的文件
$allFiles = Get-ChildItem -Path $basePath -Filter "*.md" -Recurse -File |
    Where-Object {
        $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak|tools)" -and
        $_.Name -notmatch "^00-" -and
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
    foreach ($wrong in $correctionRules.Keys) {
        $correct = $correctionRules[$wrong]
        if ($content -match [regex]::Escape($wrong)) {
            $count = ([regex]::Matches($content, [regex]::Escape($wrong))).Count
            $content = $content -replace [regex]::Escape($wrong), $correct
            $changes += "$wrong -> $correct ($count 处)"
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

        if ($fixedCount % 50 -eq 0) {
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
    Write-Host "要实际修正，请运行: .\批量修正符号-高效版.ps1 -Backup" -ForegroundColor Cyan
} else {
    Write-Host "`n修正详情已记录到变量 `$processedFiles" -ForegroundColor Cyan
}

return $processedFiles
