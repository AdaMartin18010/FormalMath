# FormalMath项目生成数学家索引脚本
# 创建日期: 2025年12月31日
# 用途: 生成数学家索引

$basePath = Split-Path -Parent $PSScriptRoot

Write-Host "开始生成数学家索引..." -ForegroundColor Green

# 读取数学家时间线索引
$timelinePath = Join-Path $basePath "数学家理念体系\00-数学家时间线索引.md"
$mathematicians = @()

if (Test-Path $timelinePath) {
    $timelineContent = Get-Content -Path $timelinePath -Raw -Encoding UTF8
    # 提取数学家名称和链接
    $mathLinks = [regex]::Matches($timelineContent, "\[([^\]]+)\]\(([^\)]+)\)")

    foreach ($match in $mathLinks) {
        $mathName = $match.Groups[1].Value
        $mathPath = $match.Groups[2].Value

        # 检查是否是数学家文档
        if ($mathPath -match "数学家理念体系" -or $mathPath -match "\.md$") {
            $mathematicians += [PSCustomObject]@{
                Name = $mathName
                Path = $mathPath
            }
        }
    }
}

# 扫描数学家理念体系目录
$mathDir = Join-Path $basePath "数学家理念体系"
if (Test-Path $mathDir) {
    $mathFiles = Get-ChildItem -Path $mathDir -Filter "*.md" -Recurse -File |
        Where-Object {
            $_.FullName -notmatch "(00-归档|99-归档|node_modules|\.git|\.bak)" -and
            $_.Name -notmatch "^00-"
        }

    foreach ($file in $mathFiles) {
        $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8 -ErrorAction SilentlyContinue
        if (-not $content) { continue }

        $relativePath = $file.FullName.Replace($basePath, "").TrimStart('\').Replace('\', '/')

        # 提取文档标题作为数学家名称
        $titleMatch = [regex]::Match($content, "^#\s+(.+)$", [System.Text.RegularExpressions.RegexOptions]::Multiline)
        $title = if ($titleMatch.Success) { $titleMatch.Groups[1].Value.Trim() } else { $file.BaseName }

        # 检查是否已存在
        $exists = $mathematicians | Where-Object { $_.Name -eq $title -or $_.Path -eq $relativePath }
        if (-not $exists) {
            $mathematicians += [PSCustomObject]@{
                Name = $title
                Path = $relativePath
            }
        }
    }
}

# 去重
$uniqueMathematicians = $mathematicians | Group-Object Name | ForEach-Object {
    $first = $_.Group[0]
    [PSCustomObject]@{
        Name = $first.Name
        Path = $first.Path
    }
}

# 按名称排序
$uniqueMathematicians = $uniqueMathematicians | Sort-Object Name

# 生成索引文档
$indexFile = Join-Path $basePath "数学家理念体系\00-数学家索引-2025年12月.md"
$indexContent = @"
# FormalMath项目数学家索引

**创建日期**: 2025年12月31日
**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
**总数学家数**: $($uniqueMathematicians.Count)

---

## 📋 索引概述

本文档提供FormalMath项目中所有数学家的索引，按字母顺序排列。

---

## 📚 数学家索引

"@

foreach ($math in $uniqueMathematicians) {
    $indexContent += "- **[$($math.Name)]($($math.Path))**`n"
}

$indexContent += @"

---

## 📊 统计信息

| 项目 | 数量 |
|------|------|
| 总数学家数 | $($uniqueMathematicians.Count) |

---

## 🔍 快速查找

### 按字母顺序

"@

# 按首字母分组
$byLetter = @{}
foreach ($math in $uniqueMathematicians) {
    $firstLetter = $math.Name.Substring(0, 1).ToUpper()
    if (-not $byLetter.ContainsKey($firstLetter)) {
        $byLetter[$firstLetter] = @()
    }
    $byLetter[$firstLetter] += $math
}

foreach ($letter in ($byLetter.Keys | Sort-Object)) {
    $indexContent += "### $letter`n`n"
    foreach ($math in ($byLetter[$letter] | Sort-Object Name)) {
        $indexContent += "- [$($math.Name)]($($math.Path))`n"
    }
    $indexContent += "`n"
}

$indexContent += @"

---

**最后更新**: $(Get-Date -Format 'yyyy年MM月dd日')
"@

$indexContent | Out-File -FilePath $indexFile -Encoding UTF8
Write-Host "✓ 数学家索引已生成: $indexFile" -ForegroundColor Green
Write-Host "  总数学家数: $($uniqueMathematicians.Count)" -ForegroundColor Cyan
