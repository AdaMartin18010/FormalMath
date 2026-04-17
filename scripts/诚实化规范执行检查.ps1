# FormalMath 诚实化规范执行检查脚本
# 检查项目统计是否存在 vanity metrics

$Issues = @()

# 检查1: 银层文档是否真有银层标准内容（字数>3000）
$SilverDocs = Get-ChildItem "E:\_src\FormalMath\docs\00-银层核心课程" -Recurse -Filter "*.md"
$ShortDocs = $SilverDocs | Where-Object { $_.Length -lt 3000 }
if ($ShortDocs.Count -gt 0) {
    $Issues += "发现 $($ShortDocs.Count) 篇银层文档字数不足3KB"
}

# 检查2: 跟踪表中的完成数是否与文件系统一致
$TrackFile = "E:\_src\FormalMath\project\00-银层攻坚执行跟踪表.md"
if (Test-Path $TrackFile) {
    $TrackContent = Get-Content -Raw $TrackFile
    # 简单检查：统计"✅ 已完成"出现的次数
    $TrackCompleted = ([regex]::Matches($TrackContent, "✅\s*已完成")).Count
    $ActualDocs = $SilverDocs.Count
    if ($TrackCompleted -ne $ActualDocs) {
        $Issues += "跟踪表完成数($TrackCompleted)与文件系统($ActualDocs)不一致"
    }
}

# 检查3: 格洛腾迪克归档是否执行
$ArchiveDir = "E:\_src\FormalMath\数学家理念体系\格洛腾迪克数学理念\00-归档-2026年4月"
if (-not (Test-Path $ArchiveDir)) {
    $Issues += "格洛腾迪克归档目录尚未创建"
}

Write-Output "=========================================="
Write-Output "诚实化规范执行检查结果"
Write-Output "=========================================="
if ($Issues.Count -eq 0) {
    Write-Output "✅ 未发现 vanity metrics 或数据不一致问题"
} else {
    $Issues | ForEach-Object { Write-Output "⚠️ $_" }
}
Write-Output "=========================================="
