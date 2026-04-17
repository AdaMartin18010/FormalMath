# FormalMath 银层文档 YAML Frontmatter 批量检查脚本
$SilverDirs = @(
    "E:\_src\FormalMath\docs\00-银层核心课程\MIT-18.06-线性代数",
    "E:\_src\FormalMath\docs\00-银层核心课程\MIT-18.100A-实分析",
    "E:\_src\FormalMath\docs\00-银层核心课程\MIT-18.701-抽象代数",
    "E:\_src\FormalMath\docs\00-银层核心课程\Harvard-232br-代数几何",
    "E:\_src\FormalMath\docs\00-银层核心课程\Stanford-FOAG-基础代数几何"
)
$RequiredFields = @("title","level","course","target_courses","status","created_at")
$LevelValid = @("copper","silver","gold")
$Report = @(); $Total=0; $Pass=0; $Fail=0
foreach ($Dir in $SilverDirs) {
    if (-not (Test-Path $Dir)) { continue }
    $Files = Get-ChildItem -Path $Dir -Filter "*.md" -Recurse
    foreach ($File in $Files) {
        $Total++
        $Content = Get-Content -Raw -Path $File.FullName
        $Issues = @()
        if (-not ($Content.StartsWith("---"))) {
            $Issues += "缺少 YAML frontmatter"
        } else {
            $end = $Content.IndexOf("---", 3)
            if ($end -gt 0) {
                $Fm = $Content.Substring(3, $end-3)
                foreach ($Field in $RequiredFields) {
                    if (-not ($Fm.Contains("$Field`:"))) { $Issues += "缺少: $Field" }
                }
                if ($Fm -match "level\s*:\s*[""']?(\w+)") {
                    $Lv = $Matches[1]
                    if ($LevelValid -notcontains $Lv) { $Issues += "level无效: $Lv" }
                }
            } else { $Issues += "YAML格式错误" }
        }
        $Body = $Content.Substring($Content.LastIndexOf("---")+3).Trim()
        $CharCount = $Body.Length
        if ($CharCount -lt 3000 -and $Issues.Count -eq 0) { $Issues += "字数不足: $CharCount" }
        if ($Issues.Count -eq 0) { $Pass++ } else { $Fail++; $Report += [PSCustomObject]@{文件=$File.FullName.Replace("E:\_src\FormalMath\",""); 字数=$CharCount; 问题=($Issues -join "; ")} }
    }
}
Write-Output "=========================================="
Write-Output "银层 YAML 规范检查结果"
Write-Output "总: $Total | 通过: $Pass | 失败: $Fail | 通过率: $([math]::Round($Pass/$Total*100,2))%"
Write-Output "=========================================="
if ($Fail -gt 0) { $Report | Format-Table -AutoSize } else { Write-Output "全部通过！" }
