# FormalMath 银层攻坚完成报告自动生成器
# 在五门课程全部完成后运行

$BaseDir = "E:\_src\FormalMath\docs\00-银层核心课程"
$ReportDir = "E:\_src\FormalMath\project\00-项目进度报告\2026年04月"
$DateStr = Get-Date -Format "yyyy-MM-dd"

$Courses = @(
    @{Name="MIT 18.06 线性代数"; Dir="MIT-18.06-线性代数"; Target=15},
    @{Name="MIT 18.100A 实分析"; Dir="MIT-18.100A-实分析"; Target=8},
    @{Name="MIT 18.701 抽象代数"; Dir="MIT-18.701-抽象代数"; Target=7},
    @{Name="Harvard 232br 代数几何"; Dir="Harvard-232br-代数几何"; Target=3},
    @{Name="Stanford FOAG"; Dir="Stanford-FOAG-基础代数几何"; Target=5}
)

$Lines = @()
$Lines += "# FormalMath 银层攻坚完成报告"
$Lines += ""
$Lines += "**日期**: $DateStr"
$Lines += "**状态**: ✅ 银层攻坚全面完成"
$Lines += ""
$Lines += "---"
$Lines += ""
$Lines += "## 一、总体成果"
$Lines += ""

$TotalDone = 0
$TotalTarget = 0
$TotalChars = 0

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
    $Lines += "### $($C.Name)"
    $Lines += "- 完成度: $Done / $($C.Target) ($Pct%)"
    $Lines += "- 总字数: $([math]::Round($Chars/1KB,1)) KB"
    $Lines += "- 核心文档清单:"
    $Files | ForEach-Object { $Lines += "  - $($_.Name)" }
    $Lines += ""
}

$TotalPct = if ($TotalTarget -gt 0) { [math]::Round($TotalDone/$TotalTarget*100,1) } else { 0 }
$Lines += "---"
$Lines += ""
$Lines += "## 二、终极统计"
$Lines += ""
$Lines += "| 指标 | 数值 |"
$Lines += "|------|------|"
$Lines += "| 总文档数 | $TotalDone / $TotalTarget |"
$Lines += "| 总完成率 | $TotalPct% |"
$Lines += "| 总字符数 | $([math]::Round($TotalChars/1KB,1)) KB |"
$Lines += "| 银层达标文档 | $TotalDone |"
$Lines += ""
$Lines += "---"
$Lines += ""
$Lines += "## 三、质量指标"
$Lines += ""
$Lines += "- [ ] YAML frontmatter 100% 覆盖"
$Lines += "- [ ] 完整自然语言证明 100% 覆盖"
$Lines += "- [ ] 典型例题与完整解答 100% 覆盖"
$Lines += "- [ ] 常见误区分析 100% 覆盖"
$Lines += "- [ ] 习题及解答 ≥10道/章 达标"
$Lines += ""
$Lines += "---"
$Lines += ""
$Lines += "## 四、后续工作"
$Lines += ""
$Lines += "1. Lean4 代码补充（MIT 18.06 等）"
$Lines += "2. 三轮审校启动"
$Lines += "3. 课堂验证实施"
$Lines += "4. 金层重构持续推进"
$Lines += ""
$Lines += "---"
$Lines += ""
$Lines += "*报告自动生成于 $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")*"

$OutFile = Join-Path $ReportDir "银层攻坚完成报告-$DateStr.md"
Set-Content -Path $OutFile -Value ($Lines -join "`n") -Encoding UTF8
Write-Output "完成报告已生成: $OutFile"
