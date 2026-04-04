# FormalMath Lean4 编译验证脚本
# 用法: .\scripts\verify-build.ps1

param(
    [switch]$UpdateDeps,
    [switch]$Verbose,
    [switch]$CheckSorry
)

$ErrorActionPreference = "Stop"

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "FormalMath Lean4 编译验证脚本" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

# 检查Lean版本
Write-Host "[1/5] 检查Lean版本..." -ForegroundColor Yellow
try {
    $leanVersion = lean --version
    Write-Host "  ✓ Lean版本: $leanVersion" -ForegroundColor Green
} catch {
    Write-Host "  ✗ Lean未安装或不在PATH中" -ForegroundColor Red
    exit 1
}

# 检查Lake
Write-Host "[2/5] 检查Lake..." -ForegroundColor Yellow
try {
    $lakeVersion = lake --version
    Write-Host "  ✓ Lake可用" -ForegroundColor Green
} catch {
    Write-Host "  ✗ Lake不可用" -ForegroundColor Red
    exit 1
}

# 更新依赖（如果需要）
if ($UpdateDeps) {
    Write-Host "[3/5] 更新依赖..." -ForegroundColor Yellow
    try {
        lake update
        Write-Host "  ✓ 依赖更新完成" -ForegroundColor Green
    } catch {
        Write-Host "  ✗ 依赖更新失败: $_" -ForegroundColor Red
        Write-Host "  提示: 检查网络连接和Git配置" -ForegroundColor Yellow
    }
} else {
    Write-Host "[3/5] 跳过依赖更新 (使用 -UpdateDeps 强制更新)" -ForegroundColor Yellow
}

# 编译项目
Write-Host "[4/5] 编译项目..." -ForegroundColor Yellow
try {
    if ($Verbose) {
        lake build --verbose
    } else {
        lake build 2>&1 | ForEach-Object {
            if ($_ -match "error") {
                Write-Host "  $_" -ForegroundColor Red
            } elseif ($_ -match "warning") {
                Write-Host "  $_" -ForegroundColor Yellow
            } else {
                Write-Host "  $_" -ForegroundColor Gray
            }
        }
    }
    Write-Host "  ✓ 编译成功" -ForegroundColor Green
} catch {
    Write-Host "  ✗ 编译失败" -ForegroundColor Red
    Write-Host "  错误: $_" -ForegroundColor Red
}

# 统计sorry数量
if ($CheckSorry) {
    Write-Host "[5/5] 统计sorry数量..." -ForegroundColor Yellow
    $files = Get-ChildItem -Path "FormalMath\*.lean" -Recurse
    $totalSorry = 0
    $fileStats = @()
    
    foreach ($file in $files) {
        $content = Get-Content $file.FullName
        $sorryCount = ($content | Select-String "sorry").Count
        $totalSorry += $sorryCount
        if ($sorryCount -gt 0) {
            $fileStats += [PSCustomObject]@{
                Name = $file.Name
                SorryCount = $sorryCount
            }
        }
    }
    
    Write-Host "  总sorry数量: $totalSorry" -ForegroundColor Cyan
    Write-Host ""
    Write-Host "  按文件统计:" -ForegroundColor Yellow
    $fileStats | Sort-Object -Property SorryCount -Descending | 
        Select-Object -First 10 | 
        Format-Table -AutoSize | 
        Out-String | 
        Write-Host
}

Write-Host ""
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "验证完成" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
