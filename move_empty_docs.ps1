# 移动空壳文档到归档目录
$archiveRoot = "e:\_src\FormalMath\00-归档\空壳文档清理-2026年4月"
$csvPath = "e:\_src\FormalMath\empty_docs_scan_v2.csv"

New-Item -ItemType Directory -Path $archiveRoot -Force | Out-Null

$records = Import-Csv $csvPath
$movedCount = 0
$moveLog = [System.Collections.ArrayList]::new()

foreach ($r in $records) {
    if ($r.Category -in @('A', 'B')) {
        $src = $r.Path
        if (-not (Test-Path $src)) {
            # 可能是相对路径存储问题，尝试组合
            if ($r.Path.StartsWith('E:')) { $src = $r.Path }
            else { $src = Join-Path "e:\_src\FormalMath" $r.Path }
        }
        
        if (Test-Path $src) {
            # 计算目标路径，保留相对目录结构
            $relPath = $src.Replace("e:\_src\FormalMath\", "").Replace("e:/_src/FormalMath/", "")
            $dest = Join-Path $archiveRoot $relPath
            $destDir = Split-Path $dest -Parent
            
            New-Item -ItemType Directory -Path $destDir -Force | Out-Null
            Move-Item -Path $src -Destination $dest -Force
            $movedCount++
            $null = $moveLog.Add($relPath)
        } else {
            Write-Host "WARNING: Source not found: $src"
        }
    }
}

$moveLog | Out-File -FilePath (Join-Path $archiveRoot "_移动清单.txt") -Encoding UTF8
Write-Host "Moved $movedCount files to archive."
