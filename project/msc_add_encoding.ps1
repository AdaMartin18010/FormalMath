# MSC编码补充脚本
# 为缺失编码的文档补充MSC编码

$encodingRules = @{
    # 格洛腾迪克相关
    "结构主义数学哲学" = @("00A30", @("00A99", "03A05"))
    "范畴论方法论" = @("18-XX", @("18Axx", "18Bxx", "18Fxx"))
    "概形理论核心思想" = @("14-XX", @("14Fxx", "14Axx"))
    "Topos理论与逻辑" = @("18B25", @("03G30", "18F10"))
    "层上同调" = @("14F05", @("14Fxx", "18F20"))
    "平展上同调" = @("14F20", @("14Fxx", "14Gxx"))
    "概形理论" = @("14-XX", @("14Axx", "14Fxx"))
    " motives理论" = @("14C15", @("14F42"))
    "黎曼-罗赫定理" = @("14C40", @("14Fxx", "19E20"))
    
    # 代数相关
    "群论" = @("20-XX", @("20Axx", "20Fxx"))
    "环论" = @("16-XX", @("16Dxx", "16Exx"))
    "域论" = @("12-XX", @("12Fxx", "12Exx"))
    "同调代数" = @("18Gxx", @("13Dxx", "16Exx"))
    "交换代数" = @("13-XX", @("13Axx", "13Cxx"))
    
    # 分析相关
    "实分析" = @("26-XX", @("26Axx", "26Bxx"))
    "复分析" = @("30-XX", @("30Axx", "30Dxx"))
    "泛函分析" = @("46-XX", @("46Axx", "46Bxx"))
    
    # 几何拓扑
    "代数几何" = @("14-XX", @("14Axx", "14Fxx"))
    "代数拓扑" = @("55-XX", @("55Nxx", "55Uxx"))
    "微分几何" = @("53-XX", @("53Axx", "53Cxx"))
    
    # 数论
    "代数数论" = @("11-XX", @("11Rxx", "11Sxx"))
    "算术几何" = @("14Gxx", @("11Gxx", "14Fxx"))
    
    # 逻辑
    "数理逻辑" = @("03-XX", @("03Bxx", "03Fxx"))
    "集合论" = @("03Exx", @("03Exx"))
}

$addedCount = 0
$processedFiles = @()

Write-Host "=== 开始为缺失编码的文档补充MSC编码 ===" -ForegroundColor Green

# 1. 处理格洛腾迪克核心理论文档
$grotDir = "e:\_src\FormalMath\数学家理念体系\格洛腾迪克数学理念\01-核心理论"
if(Test-Path $grotDir) {
    $files = Get-ChildItem -Path $grotDir -Filter "*.md"
    foreach($file in $files) {
        $content = Get-Content $file.FullName -Raw
        if($content -notmatch "^msc_primary:") {
            # 根据文件名匹配MSC编码
            $matched = $false
            foreach($key in $encodingRules.Keys) {
                if($file.Name -match $key) {
                    $primary = $encodingRules[$key][0]
                    $secondary = $encodingRules[$key][1]
                    $frontMatter = "---`nmsc_primary: `"$primary`"`nmsc_secondary: $($secondary | ConvertTo-Json -Compress)`n---`n`n"
                    $newContent = $frontMatter + ($content -replace "^---[\s\S]*?---\s*", "")
                    Set-Content -Path $file.FullName -Value $newContent -NoNewline
                    $addedCount++
                    $processedFiles += "格洛腾迪克/核心理论/$($file.Name) → $primary"
                    Write-Host "  已添加: 格洛腾迪克/核心理论/$($file.Name) → $primary" -ForegroundColor Yellow
                    $matched = $true
                    break
                }
            }
            if(-not $matched) {
                # 默认添加00A99
                $frontMatter = "---`nmsc_primary: `"00A99`"`nmsc_secondary: ['14-XX', '18-XX']`n---`n`n"
                $newContent = $frontMatter + ($content -replace "^---[\s\S]*?---\s*", "")
                if($content -notmatch "^---") {
                    $newContent = $frontMatter + $content
                }
                Set-Content -Path $file.FullName -Value $newContent -NoNewline
                $addedCount++
                $processedFiles += "格洛腾迪克/核心理论/$($file.Name) → 00A99 (默认)"
                Write-Host "  已添加: 格洛腾迪克/核心理论/$($file.Name) → 00A99 (默认)" -ForegroundColor DarkYellow
            }
        }
    }
}

# 2. 处理格洛腾迪克数学内容深度分析文档
$mathContentDir = "e:\_src\FormalMath\数学家理念体系\格洛腾迪克数学理念\02-数学内容深度分析"
if(Test-Path $mathContentDir) {
    # 获取所有子目录中的md文件
    $files = Get-ChildItem -Path $mathContentDir -Recurse -Filter "*.md" | Where-Object { 
        $_.Name -match "(层上同调|平展上同调|概形|黎曼-罗赫|对偶性|范畴|函子| motives|拓扑斯)"
    } | Select-Object -First 30
    
    foreach($file in $files) {
        $content = Get-Content $file.FullName -Raw
        if($content -notmatch "^msc_primary:") {
            $matched = $false
            foreach($key in $encodingRules.Keys) {
                if($file.Name -match $key -or $file.FullName -match $key) {
                    $primary = $encodingRules[$key][0]
                    $secondary = $encodingRules[$key][1]
                    $frontMatter = "---`nmsc_primary: `"$primary`"`nmsc_secondary: $($secondary | ConvertTo-Json -Compress)`n---`n`n"
                    if($content -match "^---") {
                        $newContent = $frontMatter + ($content -replace "^---[\s\S]*?---\s*", "")
                    } else {
                        $newContent = $frontMatter + $content
                    }
                    Set-Content -Path $file.FullName -Value $newContent -NoNewline
                    $addedCount++
                    $processedFiles += "$($file.FullName.Replace('e:\_src\FormalMath\数学家理念体系\格洛腾迪克数学理念\', '')) → $primary"
                    Write-Host "  已添加: $($file.Name) → $primary" -ForegroundColor Yellow
                    $matched = $true
                    break
                }
            }
            if(-not $matched) {
                # 根据路径判断
                if($file.FullName -match "范畴论") {
                    $primary = "18-XX"
                    $secondary = @("18Axx", "18Fxx")
                } elseif($file.FullName -match "概形") {
                    $primary = "14-XX"
                    $secondary = @("14Axx", "14Fxx")
                } elseif($file.FullName -match "同调") {
                    $primary = "14F05"
                    $secondary = @("14Fxx", "18Gxx")
                } else {
                    $primary = "00A99"
                    $secondary = @("14-XX", "18-XX")
                }
                $frontMatter = "---`nmsc_primary: `"$primary`"`nmsc_secondary: $($secondary | ConvertTo-Json -Compress)`n---`n`n"
                if($content -match "^---") {
                    $newContent = $frontMatter + ($content -replace "^---[\s\S]*?---\s*", "")
                } else {
                    $newContent = $frontMatter + $content
                }
                Set-Content -Path $file.FullName -Value $newContent -NoNewline
                $addedCount++
                $processedFiles += "$($file.Name) → $primary (路径推断)"
                Write-Host "  已添加: $($file.Name) → $primary (路径推断)" -ForegroundColor DarkYellow
            }
        }
    }
}

# 3. 处理其他关键数学家文档
$keyMathematicians = @(
    @{ Name = "欧几里得"; Primary = "51-XX"; Secondary = @("51Mxx", "01A20") },
    @{ Name = "阿基米德"; Primary = "01A20"; Secondary = @("51Mxx", "53Axx") },
    @{ Name = "牛顿"; Primary = "01A45"; Secondary = @("70-03", "00A99") },
    @{ Name = "莱布尼茨"; Primary = "01A45"; Secondary = @("03A05", "00A99") },
    @{ Name = "欧拉"; Primary = "01A50"; Secondary = @("11-03", "00A99") },
    @{ Name = "高斯"; Primary = "01A55"; Secondary = @("11-03", "51-03") },
    @{ Name = "黎曼"; Primary = "01A55"; Secondary = @("30-03", "53-03", "11Mxx") },
    @{ Name = "伽罗瓦"; Primary = "01A55"; Secondary = @("12-03", "20-03") },
    @{ Name = "康托尔"; Primary = "01A55"; Secondary = @("03E20", "03-03") },
    @{ Name = "庞加莱"; Primary = "01A55"; Secondary = @("55-03", "37-03") },
    @{ Name = "希尔伯特"; Primary = "01A60"; Secondary = @("03-03", "46-03") },
    @{ Name = "哥德尔"; Primary = "01A60"; Secondary = @("03Fxx", "03-03") },
    @{ Name = "图灵"; Primary = "01A60"; Secondary = @("68Qxx", "03Dxx") },
    @{ Name = "冯诺依曼"; Primary = "01A60"; Secondary = @("46-03", "68-03") },
    @{ Name = "诺特"; Primary = "01A60"; Secondary = @("13-03", "16-03") }
)

foreach($math in $keyMathematicians) {
    $dir = "e:\_src\FormalMath\数学家理念体系\$($math.Name)数学理念"
    if(Test-Path $dir) {
        # 为README添加MSC编码
        $readmePath = Join-Path $dir "README.md"
        if(Test-Path $readmePath) {
            $content = Get-Content $readmePath -Raw
            if($content -notmatch "^msc_primary:") {
                $frontMatter = "---`nmsc_primary: `"$($math.Primary)`"`nmsc_secondary: $($math.Secondary | ConvertTo-Json -Compress)`n---`n`n"
                if($content -match "^---") {
                    $newContent = $frontMatter + ($content -replace "^---[\s\S]*?---\s*", "")
                } else {
                    $newContent = $frontMatter + $content
                }
                Set-Content -Path $readmePath -Value $newContent -NoNewline
                $addedCount++
                $processedFiles += "$($math.Name)/README → $($math.Primary)"
                Write-Host "  已添加: $($math.Name)/README → $($math.Primary)" -ForegroundColor Green
            }
        }
    }
}

Write-Host "`n=== 编码补充完成 ===" -ForegroundColor Green
Write-Host "共添加编码文档: $addedCount" -ForegroundColor Cyan

# 导出处理列表
$processedFiles | Out-File "e:\_src\FormalMath\project\msc_added_files.txt"
Write-Host "详细列表已保存到: project\msc_added_files.txt" -ForegroundColor Green
