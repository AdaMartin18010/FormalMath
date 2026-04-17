$Dirs = @(
    "E:\_src\FormalMath\docs\00-银层核心课程\MIT-18.06-线性代数",
    "E:\_src\FormalMath\docs\00-银层核心课程\MIT-18.100A-实分析",
    "E:\_src\FormalMath\docs\00-银层核心课程\MIT-18.701-抽象代数",
    "E:\_src\FormalMath\docs\00-银层核心课程\Harvard-232br-代数几何",
    "E:\_src\FormalMath\docs\00-银层核心课程\Stanford-FOAG-基础代数几何"
)
$Report = @()
foreach ($Dir in $Dirs) {
    if (-not (Test-Path $Dir)) { continue }
    Get-ChildItem -Path $Dir -Filter "*.md" -Recurse | ForEach-Object {
        $Content = Get-Content -Raw -Path $_.FullName
        $HasLean = if ($Content -match "```lean4") { "YES" } else { "NO" }
        $Blocks = ([regex]::Matches($Content, "```lean4[\s\S]*?```")).Count
        $Report += [PSCustomObject]@{文件=$_.Name; 含Lean4=$HasLean; 代码块数=$Blocks}
    }
}
Write-Output "=========================================="
Write-Output "Lean4 嵌入检查结果"
Write-Output "=========================================="
$Report | Format-Table -AutoSize
