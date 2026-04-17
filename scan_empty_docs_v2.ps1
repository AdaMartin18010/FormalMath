# 扫描空壳文档脚本 v2 - 更严格检测模板化内容
param(
    [string[]]$Paths = @("docs", "concept", "数学家理念体系"),
    [string]$ExcludeDir = "格洛腾迪克"
)

$results = [System.Collections.ArrayList]::new()

# 占位符模式
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
    "占位符",
    "占位示例",
    "详见对应知识点教材",
    "详细解答过程",
    "关键技巧一",
    "关键技巧二",
    "常见错误一",
    "常见错误二",
    "相关练习一",
    "相关练习二",
    "变式1",
    "变式2",
    "答案待补充",
    "解析待补充",
    "解题思路待补充",
    "证明过程待补充"
)

# 强模板模式 - 如果文件中同时出现多个，基本可判定为空壳
$strongTemplatePatterns = @(
    "（题目内容详见对应知识点教材）",
    "（详细解答过程）",
    "（解析待补充）",
    "（答案待补充）",
    "（证明过程待补充）",
    "（解题思路待补充）",
    "关键技巧一\s*\n\s*2\.\s*关键技巧二",
    "常见错误一\s*\n\s*-\s*常见错误二",
    "相关练习一\s*\n\s*\*\*变式2：\*\*\s*相关练习二"
)

function Get-RealBodyLength($bodyText) {
    if (-not $bodyText) { return 0 }
    # 去除链接、代码、markdown标记
    $cleaned = $bodyText -replace '#+\s*', '' `
        -replace '\[([^\]]+)\]\([^)]+\)', '$1' `
        -replace '[\*\-_`\|\>\:\(\)\（\）]', ' ' `
        -replace '\d+\.\s+', ' ' `
        -replace '-\s+', ' ' `
        -replace '\s+', ' '
    $cn = [regex]::Matches($cleaned, '[\u4e00-\u9fff]').Count
    $en = [regex]::Matches($cleaned, '[a-zA-Z]{2,}').Count
    return $cn + $en
}

function Test-Placeholder($content) {
    foreach ($p in $placeholderPatterns) {
        if ($content -match [regex]::Escape($p)) { return $true }
    }
    return $false
}

function Test-StrongTemplate($content) {
    $matchCount = 0
    foreach ($p in $strongTemplatePatterns) {
        if ($content -match $p) { $matchCount++ }
    }
    return $matchCount -ge 1
}

function Get-MathKeywords($content) {
    $mathTerms = @("定理", "引理", "证明", "定义", "命题", "推论", "公式", "方程", "函数", "集合", "映射", "范畴", "同构", "同态", "拓扑", "流形", "代数", "几何", "分析", "数论", "导数", "积分", "极限", "连续", "收敛", "发散", "矩阵", "向量", "空间", "群", "环", "域", "模", "层", "上同调", "同调", "谱序列", "概形", "簇", "纤维", "态射")
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
    if ($idx % 500 -eq 0) { Write-Host "Processing $idx / $total" }
    
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
    
    $bodyLen = Get-RealBodyLength $body
    $isPlaceholder = Test-Placeholder $content
    $isStrongTemplate = Test-StrongTemplate $content
    $mathKeywords = Get-MathKeywords $content
    $lineCount = ($content -split "`r?`n").Count
    
    $category = "正常"
    $reason = ""
    
    # A类：纯空/极小文件
    if ($size -lt 100) {
        $category = "A"
        $reason = "文件大小小于100字节"
    } elseif ($size -lt 200 -and $bodyLen -lt 30) {
        $category = "A"
        $reason = "文件大小小于200字节且正文极短"
    }
    # B类：明显的空壳/模板
    elseif ($isStrongTemplate) {
        $category = "B"
        $reason = "强模板化占位内容（无实质数学推导）"
    }
    elseif ($isPlaceholder -and $bodyLen -lt 100) {
        $category = "B"
        $reason = "包含占位符且有效正文不足100字"
    }
    elseif ($hasFM -and $bodyLen -lt 50) {
        $category = "B"
        $reason = "有frontmatter但正文不足50字"
    }
    elseif ($bodyLen -lt 80 -and $mathKeywords -lt 3) {
        $category = "B"
        $reason = "正文过短（<80字）且无实质数学内容"
    }
    elseif ($size -lt 400 -and $bodyLen -lt 60) {
        $category = "B"
        $reason = "文件小于400字节且有效正文不足60字"
    }
    # C类：内容注水但有一定结构
    elseif ($isPlaceholder -and $mathKeywords -lt 5 -and $bodyLen -lt 200) {
        $category = "C"
        $reason = "模板化结构，数学实质稀薄，待重写"
    }
    elseif ($bodyLen -lt 120 -and $mathKeywords -lt 3 -and $lineCount -gt 15) {
        $category = "C"
        $reason = "行数多但有效内容极少，疑似注水，待重写"
    }
    
    if ($category -ne "正常") {
        $null = $results.Add([PSCustomObject]@{
            Path = $relPath
            Size = $size
            LineCount = $lineCount
            HasFrontMatter = $hasFM
            BodyLength = $bodyLen
            MathKeywords = $mathKeywords
            Placeholder = $isPlaceholder
            StrongTemplate = $isStrongTemplate
            Category = $category
            Reason = $reason
        })
    }
}

$results | Export-Csv -Path "e:\_src\FormalMath\empty_docs_scan_v2.csv" -NoTypeInformation -Encoding UTF8
Write-Host "Scan complete. Total scanned: $total"
$summary = $results | Group-Object Category | Select-Object Name, Count
$summary | Format-Table -AutoSize
Write-Host "Results saved to empty_docs_scan_v2.csv"
