# 扫描空壳文档脚本
param(
    [string[]]$Paths = @("docs", "concept", "数学家理念体系"),
    [string]$ExcludeDir = "格洛腾迪克"
)

$results = [System.Collections.ArrayList]::new()
$placeholderPatterns = @(
    "TODO",
    "待补充",
    "内容待完善",
    "正在建设中",
    "待完善",
    "待填写",
    "待编写",
    "待更新",
    "WIP",
    "Work in Progress",
    "TBD",
    "FIXME",
    "占位符"
)

$watermarkPatterns = @(
    "一、简介\s*\n\s*二、",
    "一、\s*\n\s*二、\s*\n\s*三、",
    "1\.\s*\n\s*2\.\s*\n\s*3\."
)

function Get-TextLength($text) {
    if (-not $text) { return 0 }
    # 计算中文字符 + 英文单词大致数量
    $cn = [regex]::Matches($text, '[\u4e00-\u9fff]').Count
    $en = [regex]::Matches($text, '[a-zA-Z]+').Count
    return $cn + $en
}

function Test-Placeholder($content) {
    foreach ($p in $placeholderPatterns) {
        if ($content -match [regex]::Escape($p)) { return $true }
    }
    return $false
}

function Test-Watermark($content) {
    foreach ($p in $watermarkPatterns) {
        if ($content -match $p) { return $true }
    }
    return $false
}

function Get-MathKeywords($content) {
    $mathTerms = @("定理", "引理", "证明", "定义", "命题", "推论", "公式", "方程", "函数", "集合", "映射", "范畴", "同构", "同态", "拓扑", "流形", "代数", "几何", "分析", "数论")
    $count = 0
    foreach ($t in $mathTerms) {
        $count += ([regex]::Matches($content, [regex]::Escape($t)).Count)
    }
    return $count
}

$files = @()
foreach ($p in $Paths) {
    $fp = Join-Path "e:\_src\FormalMath" $p
    $files += Get-ChildItem -Path $fp -Filter *.md -Recurse | Where-Object { 
        $_.FullName -notmatch $ExcludeDir 
    }
}

$total = $files.Count
$idx = 0
foreach ($f in $files) {
    $idx++
    if ($idx % 500 -eq 0) { Write-Host "Processing $idx / $total : $($f.FullName)" }
    
    try {
        $content = Get-Content -Raw -Path $f.FullName -Encoding UTF8
    } catch {
        try { $content = Get-Content -Raw -Path $f.FullName } catch { continue }
    }
    
    $size = $f.Length
    $relPath = $f.FullName.Replace("e:\_src\FormalMath\", "").Replace("e:/_src/FormalMath/", "")
    
    # 解析 frontmatter
    $hasFM = $false
    $body = $content
    if ($content -match '^---\s*\r?\n(?<fm>[\s\S]*?)\r?\n---\s*\r?\n(?<body>[\s\S]*)') {
        $hasFM = $true
        $body = $matches['body']
    } elseif ($content -match '^---\s*\r?\n(?<fm>[\s\S]*?)\r?\n---\s*$') {
        $hasFM = $true
        $body = ""
    }
    
    $bodyText = $body -replace '#+\s*', '' -replace '\[([^\]]+)\]\([^)]+\)', '$1' -replace '[\*\-_`\|\>]', '' -replace '\s+', ' '
    $bodyLen = Get-TextLength $bodyText
    
    $isPlaceholder = Test-Placeholder $content
    $isWatermark = Test-Watermark $content
    $mathKeywords = Get-MathKeywords $content
    
    $category = "正常"
    $reason = ""
    
    if ($size -lt 100) {
        $category = "A"
        $reason = "文件大小小于100字节"
    } elseif ($size -lt 200 -and $bodyLen -lt 30) {
        $category = "A"
        $reason = "文件大小小于200字节且正文极短"
    } elseif ($isPlaceholder -and $bodyLen -lt 80) {
        $category = "B"
        $reason = "包含占位符且正文不足80字"
    } elseif ($hasFM -and $bodyLen -lt 50) {
        $category = "B"
        $reason = "有frontmatter但正文不足50字"
    } elseif ($isWatermark -and $bodyLen -lt 100) {
        $category = "B"
        $reason = "内容高度模板化且正文不足100字"
    } elseif (($bodyLen -lt 80 -and $mathKeywords -lt 3) -or ($bodyLen -lt 40)) {
        $category = "B"
        $reason = "正文过短且无实质数学内容"
    } elseif ($isWatermark -and $mathKeywords -lt 5) {
        $category = "C"
        $reason = "模板化结构且数学关键词稀少，待重写"
    } elseif ($bodyLen -gt 200 -and $bodyLen -lt 500 -and $mathKeywords -lt 3 -and $isPlaceholder) {
        $category = "C"
        $reason = "内容注水，占位符多，数学实质少，待重写"
    }
    
    $null = $results.Add([PSCustomObject]@{
        Path = $relPath
        Size = $size
        HasFrontMatter = $hasFM
        BodyLength = $bodyLen
        MathKeywords = $mathKeywords
        Placeholder = $isPlaceholder
        Watermark = $isWatermark
        Category = $category
        Reason = $reason
    })
}

$results | Export-Csv -Path "e:\_src\FormalMath\empty_docs_scan.csv" -NoTypeInformation -Encoding UTF8
Write-Host "Scan complete. Total: $total, Results saved to empty_docs_scan.csv"
$summary = $results | Group-Object Category | Select-Object Name, Count
$summary | Format-Table -AutoSize
