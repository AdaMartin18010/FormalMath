# FormalMath 备份计划任务配置脚本
# 作者: FormalMath Dev Team
# 版本: 1.0.0
# 描述: 自动配置 Windows 任务计划程序备份任务

param(
    [switch]$RemoveExisting = $false,
    [switch]$TestOnly = $false
)

# 配置
$ScriptVersion = "1.0.0"
$ProjectRoot = "G:\_src\FormalMath\FormalMath-Enhanced"
$BackupScriptsDir = Join-Path $ProjectRoot "backup\scripts"

# 任务配置
$Tasks = @(
    @{
        Name = "FormalMath Full Backup"
        Description = "FormalMath 系统每日完整备份"
        Script = "backup.ps1"
        Arguments = '-ExecutionPolicy Bypass -File "{0}\backup.ps1" -BackupType full -RetentionDays 30' -f $BackupScriptsDir
        Schedule = @{
            Type = "Daily"
            Time = "02:00"
        }
        Settings = @{
            WakeToRun = $true
            AllowStartIfOnBatteries = $true
            DontStopIfGoingOnBatteries = $true
            StartWhenAvailable = $true
            RunOnlyIfNetworkAvailable = $false
        }
    },
    @{
        Name = "FormalMath DB Backup"
        Description = "FormalMath 数据库每小时备份"
        Script = "backup.ps1"
        Arguments = '-ExecutionPolicy Bypass -File "{0}\backup.ps1" -BackupType db -RetentionDays 7' -f $BackupScriptsDir
        Schedule = @{
            Type = "Hourly"
            Interval = 1
        }
        Settings = @{
            WakeToRun = $false
            AllowStartIfOnBatteries = $true
            DontStopIfGoingOnBatteries = $true
            StartWhenAvailable = $true
            RunOnlyIfNetworkAvailable = $false
        }
    },
    @{
        Name = "FormalMath Backup Verify"
        Description = "验证最近备份的完整性"
        Script = "verify_backup.ps1"
        Arguments = '-ExecutionPolicy Bypass -File "{0}\verify_backup.ps1" -Detailed' -f $BackupScriptsDir
        Schedule = @{
            Type = "Daily"
            Time = "06:00"
        }
        Settings = @{
            WakeToRun = $false
            AllowStartIfOnBatteries = $true
            DontStopIfGoingOnBatteries = $true
            StartWhenAvailable = $true
        }
    }
)

# 日志函数
function Write-Log {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logEntry = "[$timestamp] [$Level] $Message"
    switch ($Level) {
        "ERROR" { Write-Host $logEntry -ForegroundColor Red }
        "WARN" { Write-Host $logEntry -ForegroundColor Yellow }
        "SUCCESS" { Write-Host $logEntry -ForegroundColor Green }
        default { Write-Host $logEntry }
    }
}

# 检查管理员权限
function Test-Administrator {
    $currentUser = [Security.Principal.WindowsIdentity]::GetCurrent()
    $principal = New-Object Security.Principal.WindowsPrincipal($currentUser)
    return $principal.IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
}

# 移除现有任务
function Remove-ExistingTasks {
    Write-Log "检查并移除现有任务..."
    foreach ($task in $Tasks) {
        $existingTask = Get-ScheduledTask -TaskName $task.Name -ErrorAction SilentlyContinue
        if ($existingTask) {
            try {
                Unregister-ScheduledTask -TaskName $task.Name -Confirm:$false
                Write-Log "已移除现有任务: $($task.Name)" -Level "WARN"
            }
            catch {
                Write-Log "移除任务失败: $($task.Name) - $($_.Exception.Message)" -Level "ERROR"
            }
        }
    }
}

# 创建计划任务
function New-BackupScheduledTask {
    param([hashtable]$TaskConfig)
    
    Write-Log "创建任务: $($TaskConfig.Name)"
    
    try {
        # 创建操作
        $action = New-ScheduledTaskAction `
            -Execute "powershell.exe" `
            -Argument $TaskConfig.Arguments `
            -WorkingDirectory (Join-Path $ProjectRoot "backup")
        
        # 创建触发器
        $trigger = $null
        switch ($TaskConfig.Schedule.Type) {
            "Daily" {
                $trigger = New-ScheduledTaskTrigger `
                    -Daily `
                    -At $TaskConfig.Schedule.Time
            }
            "Hourly" {
                $trigger = New-ScheduledTaskTrigger `
                    -Once `
                    -At (Get-Date) `
                    -RepetitionInterval (New-TimeSpan -Hours $TaskConfig.Schedule.Interval) `
                    -RepetitionDuration (New-TimeSpan -Days 3650)
            }
        }
        
        # 创建设置
        $settings = New-ScheduledTaskSettingsSet `
            -WakeToRun:$TaskConfig.Settings.WakeToRun `
            -AllowStartIfOnBatteries:$TaskConfig.Settings.AllowStartIfOnBatteries `
            -DontStopIfGoingOnBatteries:$TaskConfig.Settings.DontStopIfGoingOnBatteries `
            -StartWhenAvailable:$TaskConfig.Settings.StartWhenAvailable `
            -RunOnlyIfNetworkAvailable:$TaskConfig.Settings.RunOnlyIfNetworkAvailable
        
        # 创建主体
        $principal = New-ScheduledTaskPrincipal `
            -UserId "$env:USERDOMAIN\$env:USERNAME" `
            -LogonType Interactive `
            -RunLevel Highest
        
        # 注册任务
        if (!$TestOnly) {
            Register-ScheduledTask `
                -TaskName $TaskConfig.Name `
                -Action $action `
                -Trigger $trigger `
                -Settings $settings `
                -Principal $principal `
                -Description $TaskConfig.Description `
                -Force | Out-Null
            
            Write-Log "任务创建成功: $($TaskConfig.Name)" -Level "SUCCESS"
        } else {
            Write-Log "[TEST] 将创建任务: $($TaskConfig.Name)" -Level "WARN"
            Write-Log "[TEST]   命令: powershell.exe $($TaskConfig.Arguments)" -Level "WARN"
            Write-Log "[TEST]   计划: $($TaskConfig.Schedule.Type)" -Level "WARN"
        }
        
        return $true
    }
    catch {
        Write-Log "任务创建失败: $($task.Name) - $($_.Exception.Message)" -Level "ERROR"
        return $false
    }
}

# 显示任务状态
function Show-TaskStatus {
    Write-Log "==========================================="
    Write-Log "当前备份任务状态"
    Write-Log "==========================================="
    
    foreach ($task in $Tasks) {
        $existingTask = Get-ScheduledTask -TaskName $task.Name -ErrorAction SilentlyContinue
        if ($existingTask) {
            $taskInfo = Get-ScheduledTaskInfo -TaskName $task.Name
            $status = switch ($existingTask.State) {
                "Ready" { "就绪" }
                "Running" { "运行中" }
                "Disabled" { "已禁用" }
                default { $existingTask.State }
            }
            Write-Log "任务: $($task.Name)" -Level "SUCCESS"
            Write-Log "  状态: $status"
            Write-Log "  下次运行: $($taskInfo.NextRunTime)"
            Write-Log "  上次运行: $($taskInfo.LastRunTime)"
            Write-Log "  上次结果: $($taskInfo.LastTaskResult)"
        } else {
            Write-Log "任务: $($task.Name) - 不存在" -Level "WARN"
        }
        Write-Log ""
    }
}

# 主执行流程
function Start-Setup {
    Write-Log "==========================================="
    Write-Log "FormalMath 备份任务配置脚本 v$ScriptVersion"
    Write-Log "==========================================="
    
    # 检查管理员权限
    if (!(Test-Administrator)) {
        Write-Log "需要管理员权限运行此脚本" -Level "ERROR"
        Write-Log "请以管理员身份运行 PowerShell 后重试" -Level "ERROR"
        exit 1
    }
    
    # 检查脚本文件
    Write-Log "检查脚本文件..."
    $allScriptsExist = $true
    foreach ($task in $Tasks) {
        $scriptPath = Join-Path $BackupScriptsDir $task.Script
        if (Test-Path $scriptPath) {
            Write-Log "  ✓ $($task.Script)" -Level "SUCCESS"
        } else {
            Write-Log "  ✗ $($task.Script) - 不存在" -Level "ERROR"
            $allScriptsExist = $false
        }
    }
    
    if (!$allScriptsExist) {
        Write-Log "部分脚本文件不存在，请检查安装" -Level "ERROR"
        exit 1
    }
    
    # 移除现有任务
    if ($RemoveExisting) {
        Remove-ExistingTasks
    }
    
    # 创建任务
    Write-Log ""
    Write-Log "创建计划任务..."
    $successCount = 0
    foreach ($task in $Tasks) {
        if (New-BackupScheduledTask -TaskConfig $task) {
            $successCount++
        }
    }
    
    Write-Log ""
    Write-Log "==========================================="
    Write-Log "任务配置完成: 成功 $successCount / $($Tasks.Count)"
    Write-Log "==========================================="
    
    # 显示任务状态
    if (!$TestOnly) {
        Show-TaskStatus
    }
    
    # 提示
    Write-Log ""
    Write-Log "提示:"
    Write-Log "  - 任务将在指定时间自动运行"
    Write-Log "  - 可手动运行任务进行测试"
    Write-Log "  - 查看日志: G:\_src\FormalMath\FormalMath-Enhanced\backup\logs\"
    Write-Log "  - 管理任务: 任务计划程序 → 任务计划程序库"
}

# 执行设置
try {
    Start-Setup
}
catch {
    Write-Log "配置过程中发生错误: $($_.Exception.Message)" -Level "ERROR"
    exit 1
}
