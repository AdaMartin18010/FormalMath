# FormalMath 按文档生成跨分支链接索引
# 设计文档: project/00-跨分支链接系统设计文档-2026年2月.md
# 用途: 从 cross-branch-links.yaml 生成「入链/出链」按文档聚合的索引页

param(
    [string]$LinksFile = "project/links/cross-branch-links.yaml",
    [string]$OutputFile = "project/links/01-按文档链接索引.md",
    [string]$Root = (Split-Path -Parent $PSScriptRoot)
)

$linksPath = Join-Path $Root $LinksFile
$outPath = Join-Path $Root $OutputFile

if (-not (Test-Path $linksPath)) {
    Write-Host "未找到链接文件: $linksPath" -ForegroundColor Red
    exit 1
}

$content = Get-Content -Path $linksPath -Raw -Encoding UTF8

# 解析 YAML：提取 id, source, target, type, description（排除双引号、#、换行）
$idMatches = [regex]::Matches($content, '(?m)^\s+id:\s*(.+)$')
$srcMatches = [regex]::Matches($content, '(?m)^\s+source:\s*"([^"]+)"')
$tgtMatches = [regex]::Matches($content, '(?m)^\s+target:\s*"([^"]+)"')
$typeMatches = [regex]::Matches($content, '(?m)^\s+type:\s*"([^"]+)"')
$descMatches = [regex]::Matches($content, '(?m)^\s+description:\s*"([^"]*)"')

$n = $idMatches.Count
if ($n -eq 0) {
    $n = [Math]::Max($srcMatches.Count, $tgtMatches.Count)
}

$links = @()
for ($i = 0; $i -lt $n; $i++) {
    $src = if ($i -lt $srcMatches.Count) { $srcMatches[$i].Groups[1].Value.Trim() } else { "" }
    $tgt = if ($i -lt $tgtMatches.Count) { $tgtMatches[$i].Groups[1].Value.Trim() } else { "" }
    if (-not $src -or -not $tgt) { continue }
    $links += @{
        id   = if ($i -lt $idMatches.Count) { $idMatches[$i].Groups[1].Value.Trim() } else { "L$($i+1)" }
        source = $src
        target = $tgt
        type  = if ($i -lt $typeMatches.Count) { $typeMatches[$i].Groups[1].Value.Trim() } else { "" }
        desc  = if ($i -lt $descMatches.Count) { $descMatches[$i].Groups[1].Value.Trim() } else { "" }
    }
}

# 按文档聚合：出链（以该文档为 source）、入链（以该文档为 target）
$bySource = @{}
$byTarget = @{}
$allDocs = [System.Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
foreach ($l in $links) {
    [void]$allDocs.Add($l.source)
    [void]$allDocs.Add($l.target)
    if (-not $bySource[$l.source]) { $bySource[$l.source] = @() }
    $bySource[$l.source] += $l
    if (-not $byTarget[$l.target]) { $byTarget[$l.target] = @() }
    $byTarget[$l.target] += $l
}

$sortedDocs = [string[]]($allDocs | Sort-Object)

$sb = [System.Text.StringBuilder]::new()
[void]$sb.AppendLine("# 按文档链接索引（跨分支链接）")
[void]$sb.AppendLine("")
[void]$sb.AppendLine("**生成方式**：由 [cross-branch-links.yaml](./cross-branch-links.yaml) 经 [tools/生成按文档链接索引.ps1](../../tools/生成按文档链接索引.ps1) 自动生成。")
[void]$sb.AppendLine("**数据源**：[00-链接导航索引](./00-链接导航索引.md) 与 [00-跨分支链接系统设计文档](../00-跨分支链接系统设计文档-2026年2月2日.md)。")
[void]$sb.AppendLine("")
[void]$sb.AppendLine("---")
[void]$sb.AppendLine("")
[void]$sb.AppendLine("## 说明")
[void]$sb.AppendLine("")
[void]$sb.AppendLine("- **出链**：以该文档为**源**的链接（本文档指向的其他文档）。")
[void]$sb.AppendLine("- **入链**：以该文档为**目标**的链接（其他文档指向本文档）。")
[void]$sb.AppendLine("- 路径均为相对项目根。")
[void]$sb.AppendLine("")
[void]$sb.AppendLine("---")
[void]$sb.AppendLine("")

foreach ($doc in $sortedDocs) {
    $outLinks = $bySource[$doc]
    $inLinks = $byTarget[$doc]
    if (-not $outLinks -and -not $inLinks) { continue }

    [void]$sb.AppendLine("## $doc")
    [void]$sb.AppendLine("")

    if ($outLinks -and $outLinks.Count -gt 0) {
        [void]$sb.AppendLine("### 出链（$($outLinks.Count) 条）")
        [void]$sb.AppendLine("")
        [void]$sb.AppendLine("| 目标 | 类型 | 说明 |")
        [void]$sb.AppendLine("|------|------|------|")
        foreach ($l in $outLinks) {
            $desc = $l.desc -replace '\|', '&#124;' -replace "`n", " "
            $typ = $l.type
            [void]$sb.AppendLine("| $($l.target) | $typ | $desc |")
        }
        [void]$sb.AppendLine("")
    }

    if ($inLinks -and $inLinks.Count -gt 0) {
        [void]$sb.AppendLine("### 入链（$($inLinks.Count) 条）")
        [void]$sb.AppendLine("")
        [void]$sb.AppendLine("| 源 | 类型 | 说明 |")
        [void]$sb.AppendLine("|------|------|------|")
        foreach ($l in $inLinks) {
            $desc = $l.desc -replace '\|', '&#124;' -replace "`n", " "
            $typ = $l.type
            [void]$sb.AppendLine("| $($l.source) | $typ | $desc |")
        }
        [void]$sb.AppendLine("")
    }

    [void]$sb.AppendLine("---")
    [void]$sb.AppendLine("")
}

$dir = Split-Path -Parent $outPath
if (-not (Test-Path $dir)) { New-Item -ItemType Directory -Path $dir -Force | Out-Null }
Set-Content -Path $outPath -Value $sb.ToString() -Encoding UTF8 -NoNewline
$sb = $null

Write-Host "已生成: $outPath (文档数 $($sortedDocs.Count), 链接数 $($links.Count))" -ForegroundColor Green
exit 0
