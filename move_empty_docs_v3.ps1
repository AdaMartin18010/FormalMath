# 移动空壳文档到归档目录 v3
$archiveRoot = "e:\_src\FormalMath\00-归档\空壳文档清理-2026年4月"
$csvPath = "e:\_src\FormalMath\empty_docs_scan_v2.csv"

New-Item -ItemType Directory -Path $archiveRoot -Force -ErrorAction SilentlyContinue | Out-Null

$records = Import-Csv $csvPath
$movedCount = 0
$moveLog = [System.Collections.ArrayList]::new()

foreach ($r in $records) {
    if ($r.Category -in @('A', 'B')) {
        $src = $r.Path.Replace("/", "\")
        
        # 如果CSV路径是相对路径（不含盘符），拼接根目录
        if (-not ($src -match '^[A-Za-z]:\\')) {
            $src = Join-Path "e:\_src\FormalMath" $src
        }
        
        if (Test-Path $src) {
            # 计算相对路径（从项目根开始）
            $absRoot = (Resolve-Path "e:\_src\FormalMath").Path
            $absSrc = (Resolve-Path $src).Path
            $rel = $absSrc.Substring($absRoot.Length + 1)
            
            $dest = Join-Path $archiveRoot $rel
            $destDir = [System.IO.Path]::GetDirectoryName($dest)
            
            if (-not (Test-Path $destDir)) {
                [void][System.IO.Directory]::CreateDirectory($destDir)
            }
            
            [System.IO.File]::Copy($absSrc, $dest, $true)
            [System.IO.File]::Delete($absSrc)
            
            $movedCount++
            $null = $moveLog.Add($rel)
        } else {
            Write-Host "WARNING: Source not found: $src"
        }
    }
}

$moveLog | Out-File -FilePath (Join-Path $archiveRoot "_移动清单.txt") -Encoding UTF8
Write-Host "Moved $movedCount files to archive."
