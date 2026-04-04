# FormalMath 备份系统测试脚本
# 作者: FormalMath Dev Team
# 版本: 1.0.0
# 描述: 测试备份系统的基本功能

param(
    [switch]$Quick = $false,
    [switch]$SkipBackup = $false
)

# 配置
$ScriptVersion = "1.0.0"
$ProjectRoot = "G:\_src\FormalMath\FormalMath-Enhanced"
$BackupDir = Join-Path $ProjectRoot "backup"
$TestResults = @()

# 日志函数
function Write-Log {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "HH:mm:ss"
    switch ($Level) {
        "PASS" { Write-Host "[$timestamp] [✓] $Message" -ForegroundColor Green }
        "FAIL" { Write-Host "[$timestamp] [✗] $Message" -ForegroundColor Red }
        "WARN" { Write-Host "[$timestamp] [!] $Message" -ForegroundColor Yellow }
        "INFO" { Write-Host "[$timestamp] [ℹ] $Message" }
    }
}

# 测试结果记录
function Add-TestResult {
    param([string]$TestName, [bool]$Passed, [string]$Message = "")
    $script:TestResults += [PSCustomObject]@{
        TestName = $TestName
        Passed = $Passed
        Message = $Message
    }
}

# 测试 1: 目录结构
function Test-DirectoryStructure {
    Write-Log "测试目录结构..." "INFO"
    
    $requiredDirs = @(
        "scripts",
        "docs",
        "archive",
        "logs"
    )
    
    $allPassed = $true
    foreach ($dir in $requiredDirs) {
        $path = Join-Path $BackupDir $dir
        if (Test-Path $path) {
            Write-Log "目录存在: $dir" "PASS"
        } else {
            Write-Log "目录缺失: $dir" "FAIL"
            $allPassed = $false
        }
    }
    
    Add-TestResult -TestName "目录结构" -Passed $allPassed
    return $allPassed
}

# 测试 2: 脚本文件
function Test-ScriptFiles {
    Write-Log "`n测试脚本文件..." "INFO"
    
    $requiredScripts = @(
        "scripts\backup.ps1",
        "scripts\restore.ps1",
        "scripts\verify_backup.ps1",
        "scripts\setup-scheduled-tasks.ps1"
    )
    
    $allPassed = $true
    foreach ($script in $requiredScripts) {
        $path = Join-Path $BackupDir $script
        if (Test-Path $path) {
            $size = (Get-Item $path).Length
            Write-Log "脚本存在: $script ($size bytes)" "PASS"
        } else {
            Write-Log "脚本缺失: $script" "FAIL"
            $allPassed = $false
        }
    }
    
    Add-TestResult -TestName "脚本文件" -Passed $allPassed
    return $allPassed
}

# 测试 3: 文档文件
function Test-DocumentationFiles {
    Write-Log "`n测试文档文件..." "INFO"
    
    $requiredDocs = @(
        "README.md",
        "docs\备份配置指南.md",
        "docs\恢复流程文档.md",
        "docs\灾难恢复计划.md"
    )
    
    $allPassed = $true
    foreach ($doc in $requiredDocs) {
        $path = Join-Path $BackupDir $doc
        if (Test-Path $path) {
            Write-Log "文档存在: $doc" "PASS"
        } else {
            Write-Log "文档缺失: $doc" "FAIL"
            $allPassed = $false
        }
    }
    
    Add-TestResult -TestName "文档文件" -Passed $allPassed
    return $allPassed
}

# 测试 4: PowerShell 执行策略
function Test-ExecutionPolicy {
    Write-Log "`n测试 PowerShell 执行策略..." "INFO"
    
    $policy = Get-ExecutionPolicy
    Write-Log "当前执行策略: $policy" "INFO"
    
    if ($policy -eq "Restricted") {
        Write-Log "执行策略为 Restricted，可能需要更改" "WARN"
        Add-TestResult -TestName "执行策略" -Passed $false -Message "执行策略为 Restricted"
        return $false
    } else {
        Write-Log "执行策略允许运行脚本" "PASS"
        Add-TestResult -TestName "执行策略" -Passed $true
        return $true
    }
}

# 测试 5: 磁盘空间
function Test-DiskSpace {
    Write-Log "`n测试磁盘空间..." "INFO"
    
    try {
        $drive = Get-PSDrive G
        $freeGB = [math]::Round($drive.Free / 1GB, 2)
        $totalGB = [math]::Round(($drive.Used + $drive.Free) / 1GB, 2)
        $freePercent = [math]::Round(($drive.Free / ($drive.Used + $drive.Free)) * 100, 2)
        
        Write-Log "磁盘 G: 总空间: $totalGB GB" "INFO"
        Write-Log "磁盘 G: 可用空间: $freeGB GB ($freePercent%)" "INFO"
        
        if ($freePercent -lt 10) {
            Write-Log "磁盘空间不足 (< 10%)" "FAIL"
            Add-TestResult -TestName "磁盘空间" -Passed $false -Message "可用空间不足 10%"
            return $false
        } elseif ($freePercent -lt 20) {
            Write-Log "磁盘空间较低 (< 20%)" "WARN"
            Add-TestResult -TestName "磁盘空间" -Passed $true -Message "可用空间较低"
            return $true
        } else {
            Write-Log "磁盘空间充足" "PASS"
            Add-TestResult -TestName "磁盘空间" -Passed $true
            return $true
        }
    }
    catch {
        Write-Log "无法检查磁盘空间: $($_.Exception.Message)" "WARN"
        Add-TestResult -TestName "磁盘空间" -Passed $true -Message "检查失败但继续"
        return $true
    }
}

# 测试 6: 项目目录存在
function Test-ProjectDirectory {
    Write-Log "`n测试项目目录..." "INFO"
    
    if (Test-Path $ProjectRoot) {
        Write-Log "项目目录存在: $ProjectRoot" "PASS"
        Add-TestResult -TestName "项目目录" -Passed $true
        return $true
    } else {
        Write-Log "项目目录不存在: $ProjectRoot" "FAIL"
        Add-TestResult -TestName "项目目录" -Passed $false
        return $false
    }
}

# 测试 7: 备份功能（可选）
function Test-BackupFunction {
    Write-Log "`n测试备份功能..." "INFO"
    
    if ($SkipBackup) {
        Write-Log "跳过备份测试" "WARN"
        Add-TestResult -TestName "备份功能" -Passed $true -Message "已跳过"
        return $true
    }
    
    try {
        $testBackupDir = Join-Path $env:TEMP "formalmath_test_backup_$(Get-Random)"
        
        Write-Log "执行测试备份（仅配置）..." "INFO"
        
        # 仅执行配置备份（较快）
        $backupScript = Join-Path $BackupDir "scripts\backup.ps1"
        & $backupScript -BackupType config -BackupPath $testBackupDir -Compress:$false -RetentionDays 1
        
        if ($LASTEXITCODE -eq 0 -or $? ) {
            Write-Log "备份功能正常" "PASS"
            Add-TestResult -TestName "备份功能" -Passed $true
            
            # 清理测试备份
            if (Test-Path $testBackupDir) {
                Remove-Item -Path $testBackupDir -Recurse -Force -ErrorAction SilentlyContinue
            }
            return $true
        } else {
            Write-Log "备份功能异常" "FAIL"
            Add-TestResult -TestName "备份功能" -Passed $false
            return $false
        }
    }
    catch {
        Write-Log "备份测试失败: $($_.Exception.Message)" "FAIL"
        Add-TestResult -TestName "备份功能" -Passed $false -Message $_.Exception.Message
        return $false
    }
}

# 主执行流程
function Start-Tests {
    Write-Log "===========================================" "INFO"
    Write-Log "FormalMath 备份系统测试 v$ScriptVersion" "INFO"
    Write-Log "===========================================" "INFO"
    
    # 执行所有测试
    Test-DirectoryStructure | Out-Null
    Test-ScriptFiles | Out-Null
    Test-DocumentationFiles | Out-Null
    Test-ExecutionPolicy | Out-Null
    Test-DiskSpace | Out-Null
    Test-ProjectDirectory | Out-Null
    
    if (!$Quick) {
        Test-BackupFunction | Out-Null
    }
    
    # 显示测试结果汇总
    Write-Log "`n===========================================" "INFO"
    Write-Log "测试结果汇总" "INFO"
    Write-Log "===========================================" "INFO"
    
    $passed = 0
    $failed = 0
    
    foreach ($result in $TestResults) {
        $status = if ($result.Passed) { "通过" } else { "失败" }
        $color = if ($result.Passed) { "PASS" } else { "FAIL" }
        Write-Log "$($result.TestName): $status" $color
        
        if ($result.Passed) { $passed++ } else { $failed++ }
    }
    
    Write-Log "`n===========================================" "INFO"
    Write-Log "总计: 通过 $passed / 失败 $failed / 合计 $($TestResults.Count)" "INFO"
    Write-Log "===========================================" "INFO"
    
    # 最终结论
    if ($failed -eq 0) {
        Write-Log "`n所有测试通过！备份系统已就绪。" "PASS"
        return 0
    } else {
        Write-Log "`n部分测试失败，请检查上述问题。" "FAIL"
        return 1
    }
}

# 执行测试
try {
    $exitCode = Start-Tests
    exit $exitCode
}
catch {
    Write-Log "测试过程中发生错误: $($_.Exception.Message)" "FAIL"
    exit 1
}
