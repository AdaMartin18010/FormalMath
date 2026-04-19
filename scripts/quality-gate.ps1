# FormalMath 本地质量检查脚本

Write-Host "=== FormalMath Quality Gate ==="

# 1. Count silver docs
$silverCount = (Get-ChildItem docs -Recurse -Filter "*.md" | Where-Object { 
    (Get-Content $_.FullName -Raw) -match 'level:\s*"?silver"?' 
} | Measure-Object).Count
Write-Host "Silver docs: $silverCount (target: >= 197)"

# 2. Check Lean4 build
Write-Host "
=== Lean4 Build Check ==="
cd docs\09-形式化证明\Lean4
lake build 2>&1 | Select-Object -Last 5
cd ..\..\..

# 3. Check missing references
$missingRefs = (Get-ChildItem docs -Recurse -Filter "*.md" | Where-Object { 
    $_.FullName -notmatch '00-归档' -and 
    (Get-Content $_.FullName -Raw) -match 'level:\s*"?silver"?' -and
    (Get-Content $_.FullName -Raw) -notmatch '## 参考文献'
} | Measure-Object).Count
Write-Host "
Missing references: $missingRefs (target: 0)"

# 4. Check draft status
$draftCount = (Get-ChildItem docs -Recurse -Filter "*.md" | Where-Object { 
    (Get-Content $_.FullName -Raw) -match 'level:\s*"?silver"?' -and
    (Get-Content $_.FullName -Raw) -match 'review_status:\s*"?draft"?'
} | Measure-Object).Count
Write-Host "Draft silver docs: $draftCount (target: 0)"

Write-Host "
=== Quality Gate Complete ==="