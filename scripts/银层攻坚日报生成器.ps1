# FormalMath 银层攻坚日报生成器
# 自动统计各课程产出并生成 Markdown 日报

$BaseDir = "E:\_src\FormalMath\docs\00-银层核心课程"
$ReportDir = "E:\_src\FormalMath\project\00-项目进度报告\2026年04月"
if (-not (Test-Path $ReportDir)) { New-Item -ItemType Directory -Path $ReportDir -Force }

$DateStr = Get-Date -Format "yyyy-MM-dd"
$Courses = @(
    @{Name="MIT 18.06 线性代数"; Dir="MIT-18.06-线性代数"; Target=15},
    @{Name="MIT 18.100A 实分析"; Dir="MIT-18.100A-实分析"; Target=8},
    @{Name="MIT 18.701 抽象代数"; Dir="MIT-18.701-抽象代数"; Target=7},
    @{Name="Harvard 232br 代数几何"; Dir="Harvard-232br-代数几何"; Target=3},
    @{Name="Stanford FOAG"; Dir="Stanford-FOAG-基础代数几何"; Target=5}
)

$Lines = @()
$Lines += "# 银层攻坚日报 — $DateStr"
$Lines += ""
$Lines += "| 课程 | 已完成 | 目标 | 进度 | 今日新增 | 总字数 |"
$Lines += "|------|--------|------|------|----------|--------|"

$TotalDone = 0
$TotalTarget = 0
$TotalChars = 0
$TotalNew = 0

foreach ($C in $Courses) {
    $DirPath = Join-Path $BaseDir $C.Dir
    if (Test-Path $DirPath) {
        $Files = Get-ChildItem -Path $DirPath -Filter "*.md" -Recurse | Where-Object { $_.Name -notmatch "INDEX|README" }
        $Done = $Files.Count
        $Chars = ($Files | Measure-Object -Property Length -Sum).Sum
        $TotalChars += $Chars
    } else {
        $Done = 0
        $Chars = 0
    }
    $TotalDone += $Done
    $TotalTarget += $C.Target
    $Pct = if ($C.Target -gt 0) { [math]::Round($Done/$C.Target*100,1) } else { 0 }
    $Lines += "| $($C.Name) | $Done | $($C.Target) | $Pct% | — | $([math]::Round($Chars/1KB,1)) KB |"
}

$TotalPct = if ($TotalTarget -gt 0) { [math]::Round($TotalDone/$TotalTarget*100,1) } else { 0 }
$Lines += "| **合计** | **$TotalDone** | **$TotalTarget** | **$TotalPct%** | **$TotalNew** | **$([math]::Round($TotalChars/1KB,1)) KB** |"
$Lines += ""
$Lines += "---"
$Lines += ""
$Lines += "*自动生成于 $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")*"

$OutFile = Join-Path $ReportDir "银层攻坚日报-$DateStr.md"
Set-Content -Path $OutFile -Value ($Lines -join "`n") -Encoding UTF8
Write-Output "日报已生成: $OutFile"
Write-Output "总进度: $TotalDone / $TotalTarget ($TotalPct%)"
