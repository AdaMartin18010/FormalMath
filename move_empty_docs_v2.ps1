# 移动空壳文档到归档目录 v2
$archiveRoot = "e:\_src\FormalMath\00-归档\空壳文档清理-2026年4月"
$csvPath = "e:\_src\FormalMath\empty_docs_scan_v2.csv"

New-Item -ItemType Directory -Path $archiveRoot -Force -ErrorAction SilentlyContinue | Out-Null

$records = Import-Csv $csvPath
$movedCount = 0
$moveLog = [System.Collections.ArrayList]::new()

foreach ($r in $records) {
    if ($r.Category -in @('A', 'B')) {
        $src = $r.Path
        # 标准化路径
        $src = $src.Replace("/", "\")
        if (-not $src.StartsWith("e:\")) {
            $src = Join-Path "e:\_src\FormalMath" $src
        }
        
        if (Test-Path $src) {
            # 计算相对路径
            $rel = $src.Replace("e:\_src\FormalMath\", "")
            $dest = Join-Path $archiveRoot $rel
            $destDir = [System.IO.Path]::GetDirectoryName($dest)
            
            if (-not (Test-Path $destDir)) {
                [void][System.IO.Directory]::CreateDirectory($destDir)
            }
            
            [System.IO.File]::Copy($src, $dest, $true)
            [System.IO.File]::Delete($src)
            
            $movedCount++
            $null = $moveLog.Add($rel)
        } else {
            Write-Host "WARNING: Source not found: $src"
        }
    }
}

$moveLog | Out-File -FilePath (Join-Path $archiveRoot "_移动清单.txt") -Encoding UTF8
Write-Host "Moved $movedCount files to archive."
