# FormalMath项目MSC编码批量补充脚本
# 创建日期: 2026年4月3日

param(
    [switch]$WhatIf = $false,
    [switch]$Verbose = $false
)

# 读取映射规则
$mappingRules = Get-Content -Path "project/msc_mapping_rules.json" -Raw | ConvertFrom-Json

# 统计变量
$stats = @{
    processed = 0
    skipped = 0
    errors = 0
    byCategory = @{}
}

function Get-MSCCodeFromPath {
    param([string]$FilePath)
    
    $relativePath = $FilePath.Replace((Get-Location).Path, "").TrimStart("\", "/")
    
    # 检查docs目录
    if ($relativePath -match "^docs[\\/](\d{2}-[^\\/]+)[\\/]?(.*)$") {
        $category = $matches[1]
        $subPath = $matches[2]
        
        if ($mappingRules.docs.$category) {
            $rule = $mappingRules.docs.$category
            
            # 检查子目录匹配
            foreach ($subdir in $rule.subdirs.PSObject.Properties) {
                if ($subPath -match [regex]::Escape($subdir.Name)) {
                    return $subdir.Value
                }
            }
            
            return $rule.default
        }
    }
    
    # 检查数学家理念体系
    if ($relativePath -match "^数学家理念体系[\\/]([^\\/]+)") {
        $mathematician = $matches[1] -replace "数学理念", ""
        
        # 检查特定数学家
        foreach ($spec in $mappingRules.mathematicians.specific.PSObject.Properties) {
            if ($mathematician -match [regex]::Escape($spec.Name)) {
                return $spec.Value
            }
        }
        
        return $mappingRules.mathematicians.default
    }
    
    # 检查concept目录
    if ($relativePath -match "^concept[\\/]([^\\/]+)") {
        $subdir = $matches[1]
        
        if ($mappingRules.concept.subdirs.$subdir) {
            return $mappingRules.concept.subdirs.$subdir
        }
        
        return $mappingRules.concept.default
    }
    
    return $null
}

function Add-MSCFrontmatter {
    param(
        [string]$FilePath,
        [string]$MSCCode
    )
    
    try {
        $content = Get-Content -Path $FilePath -Raw -ErrorAction Stop
        
        # 检查是否已有frontmatter
        if ($content -match '^---\s*\r?\n') {
            # 已有frontmatter，检查是否有msc_primary
            if ($content -match 'msc_primary:') {
                return "already_has_msc"
            }
            
            # 添加msc_primary到现有frontmatter
            $newContent = $content -replace '^(---\s*\r?\n)', "---`nmsc_primary: `"$MSCCode`"`n"
        } else {
            # 没有frontmatter，添加新的
            $newContent = "---`nmsc_primary: `"$MSCCode`"`n---`n`n$content"
        }
        
        if (-not $WhatIf) {
            Set-Content -Path $FilePath -Value $newContent -NoNewline -Encoding UTF8
        }
        
        return "success"
    }
    catch {
        return "error: $_"
    }
}

# 获取所有.md文件
Write-Host "=== FormalMath项目MSC编码批量补充 ===" -ForegroundColor Cyan
Write-Host "扫描所有Markdown文件..." -ForegroundColor Yellow

$allFiles = @()
$allFiles += Get-ChildItem -Path "docs" -Filter "*.md" -Recurse | Where-Object { $_.FullName -notmatch "00-归档" -and $_.FullName -notmatch "归档" }
$allFiles += Get-ChildItem -Path "concept" -Filter "*.md" -Recurse | Where-Object { $_.FullName -notmatch "00-归档" -and $_.FullName -notmatch "归档" }
$allFiles += Get-ChildItem -Path "数学家理念体系" -Filter "*.md" -Recurse | Where-Object { $_.FullName -notmatch "00-归档" -and $_.FullName -notmatch "归档" }

Write-Host "找到 $($allFiles.Count) 个Markdown文件" -ForegroundColor Green
Write-Host ""

# 处理每个文件
$results = @()

foreach ($file in $allFiles) {
    # 检查是否已有MSC编码
    $content = Get-Content -Path $file.FullName -Raw -ErrorAction SilentlyContinue
    if ($content -match 'msc_primary:') {
        $stats.skipped++
        continue
    }
    
    # 推断MSC编码
    $mscCode = Get-MSCCodeFromPath -FilePath $file.FullName
    
    if ($mscCode) {
        $result = Add-MSCFrontmatter -FilePath $file.FullName -MSCCode $mscCode
        
        $category = $mscCode.Substring(0, 2) + "-XX"
        if (-not $stats.byCategory.ContainsKey($category)) {
            $stats.byCategory[$category] = 0
        }
        
        if ($result -eq "success" -or $WhatIf) {
            $stats.processed++
            $stats.byCategory[$category]++
            
            $results += [PSCustomObject]@{
                File = $file.FullName.Replace((Get-Location).Path, "")
                MSC = $mscCode
                Status = $result
            }
            
            if ($Verbose) {
                Write-Host "[$mscCode] $($file.Name)" -ForegroundColor Green
            }
        } elseif ($result -eq "already_has_msc") {
            $stats.skipped++
        } else {
            $stats.errors++
            Write-Host "错误: $result - $($file.Name)" -ForegroundColor Red
        }
    } else {
        if ($Verbose) {
            Write-Host "无法推断: $($file.FullName)" -ForegroundColor DarkGray
        }
    }
}

# 输出统计
Write-Host ""
Write-Host "=== 处理统计 ===" -ForegroundColor Cyan
Write-Host "已处理: $($stats.processed)" -ForegroundColor Green
Write-Host "已跳过(已有MSC): $($stats.skipped)" -ForegroundColor Yellow
Write-Host "错误: $($stats.errors)" -ForegroundColor Red
Write-Host ""
Write-Host "=== 按分类统计 ===" -ForegroundColor Cyan
$stats.byCategory.GetEnumerator() | Sort-Object Name | ForEach-Object {
    Write-Host "  $($_.Key): $($_.Value)篇" -ForegroundColor White
}

# 导出结果
if ($results.Count -gt 0) {
    $results | Export-Csv -Path "project/msc_supplement_results.csv" -NoTypeInformation -Encoding UTF8
    Write-Host ""
    Write-Host "详细结果已保存至: project/msc_supplement_results.csv" -ForegroundColor Green
}

# 返回统计信息
$stats
