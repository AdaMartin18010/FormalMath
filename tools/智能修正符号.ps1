# FormalMath项目智能修正符号脚本
# 创建日期: 2025年12月31日
# 用途: 智能修正符号不一致项，基于符号规范

param(
    [string]$FilePath,
    [switch]$DryRun,
    [switch]$Backup
)

$basePath = Split-Path -Parent $PSScriptRoot

Write-Host "开始智能修正符号..." -ForegroundColor Green

# 读取符号规范
$symbolFile = Join-Path $basePath "docs\FormalMath符号使用规范.md"
$symbolMap = @{}

if (Test-Path $symbolFile) {
    $content = Get-Content -Path $symbolFile -Raw -Encoding UTF8
    # 提取符号映射：符号 -> LaTeX代码
    $symbolPattern = '\|\s*\$([^\$]+)\$\s*\|\s*`([^`]+)`\s*\|'
    $matches = [regex]::Matches($content, $symbolPattern)

    foreach ($match in $matches) {
        $symbol = $match.Groups[1].Value.Trim()
        $latexCode = $match.Groups[2].Value.Trim()
        # 提取符号名称（去除$）
        $symbolName = $symbol -replace '\$', ''
        if (-not $symbolMap.ContainsKey($symbolName)) {
            $symbolMap[$symbolName] = $latexCode
        }
    }
}

Write-Host "已加载 $($symbolMap.Count) 个标准符号" -ForegroundColor Cyan

# 常见符号修正规则
$correctionRules = @{
    # 集合符号
    '\subsetneq' = '\subset'
    '\supsetneq' = '\supset'
    '\nsubseteq' = '\not\subseteq'
    '\nsupseteq' = '\not\supseteq'

    # 运算符
    '\smallsetminus' = '\backslash'

    # 关系符号
    '\ne' = '\neq'
    '\le' = '\leq'
    '\ge' = '\geq'
}

# 处理单个文件
function Fix-SymbolsInFile {
    param([string]$File)

    $content = Get-Content -Path $File -Raw -Encoding UTF8
    $originalContent = $content
    $changes = @()

    # 应用修正规则
    foreach ($wrong in $correctionRules.Keys) {
        $correct = $correctionRules[$wrong]
        if ($content -match [regex]::Escape($wrong)) {
            $count = ([regex]::Matches($content, [regex]::Escape($wrong))).Count
            $content = $content -replace [regex]::Escape($wrong), $correct
            $changes += "  - $wrong -> $correct ($count 处)"
        }
    }

    if ($changes.Count -gt 0) {
        if (-not $DryRun) {
            if ($Backup) {
                $backupPath = $File + ".bak"
                Copy-Item -Path $File -Destination $backupPath -Force
            }
            $content | Out-File -FilePath $File -Encoding UTF8 -NoNewline
        }
        return @{
            File = $File
            Changes = $changes
            Modified = $true
        }
    }

    return @{
        File = $File
        Changes = @()
        Modified = $false
    }
}

# 处理文件或目录
if ($FilePath) {
    $targetPath = if ([System.IO.Path]::IsPathRooted($FilePath)) {
        $FilePath
    } else {
        Join-Path $basePath $FilePath
    }

    if (Test-Path $targetPath) {
        if ((Get-Item $targetPath).PSIsContainer) {
            # 目录
            $files = Get-ChildItem -Path $targetPath -Filter "*.md" -Recurse -File |
                Where-Object {
                    $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak)" -and
                    $_.Name -notmatch "^00-"
                }
        } else {
            # 单个文件
            $files = @(Get-Item $targetPath)
        }

        $results = @()
        foreach ($file in $files) {
            $result = Fix-SymbolsInFile -File $file.FullName
            $results += $result
        }

        $modified = ($results | Where-Object { $_.Modified }).Count
        $total = $results.Count

        Write-Host "`n修正完成:" -ForegroundColor Cyan
        Write-Host "  总文件数: $total" -ForegroundColor Cyan
        Write-Host "  已修正: $modified 个文件" -ForegroundColor Green

        if ($modified -gt 0) {
            Write-Host "`n修正详情:" -ForegroundColor Yellow
            foreach ($result in $results | Where-Object { $_.Modified }) {
                Write-Host "  $($result.File)" -ForegroundColor Cyan
                $result.Changes | ForEach-Object { Write-Host $_ -ForegroundColor Gray }
            }
        }

        if ($DryRun) {
            Write-Host "`n这是试运行模式，未实际修改文件。" -ForegroundColor Yellow
        }
    } else {
        Write-Host "路径不存在: $targetPath" -ForegroundColor Red
    }
} else {
    Write-Host "用法: .\智能修正符号.ps1 -FilePath <文件或目录路径> [-DryRun] [-Backup]" -ForegroundColor Yellow
    Write-Host "示例: .\智能修正符号.ps1 -FilePath 'docs\01-基础数学' -DryRun" -ForegroundColor Cyan
}
