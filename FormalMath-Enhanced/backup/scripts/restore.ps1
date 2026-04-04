# FormalMath 数据恢复脚本
# 作者: FormalMath Dev Team
# 版本: 1.0.0
# 描述: 从备份文件恢复数据

param(
    [Parameter(Mandatory=$true)]
    [string]$BackupFile,
    
    [string]$RestorePath = "",
    
    [ValidateSet("full", "db", "config", "data", "verify")]
    [string]$RestoreType = "full",
    
    [switch]$Force = $false,
    [switch]$DryRun = $false,
    [switch]$VerifyOnly = $false
)

# 配置
$ErrorActionPreference = "Stop"
$ScriptVersion = "1.0.0"
$ProjectRoot = "G:\_src\FormalMath\FormalMath-Enhanced"
$Timestamp = Get-Date -Format "yyyyMMdd_HHmmss"

# 默认恢复路径
if ([string]::IsNullOrEmpty($RestorePath)) {
    $RestorePath = $ProjectRoot
}

# 日志配置
$LogDir = Join-Path $ProjectRoot "backup\logs"
$LogFile = Join-Path $LogDir "restore_$Timestamp.log"

# 确保日志目录存在
if (!(Test-Path $LogDir)) {
    New-Item -ItemType Directory -Path $LogDir -Force | Out-Null
}

# 日志函数
function Write-Log {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logEntry = "[$timestamp] [$Level] $Message"
    Write-Host $logEntry
    Add-Content -Path $LogFile -Value $logEntry
}

# 错误处理
function Handle-Error {
    param([string]$Message)
    Write-Log -Message $Message -Level "ERROR"
    exit 1
}

# 确认提示
function Confirm-Action {
    param([string]$Message)
    
    if ($Force) {
        return $true
    }
    
    $response = Read-Host "$Message (y/N)"
    return $response -eq "y" -or $response -eq "Y"
}

# 验证备份文件
function Test-BackupFile {
    param([string]$File)
    
    Write-Log "验证备份文件..."
    
    if (!(Test-Path $File)) {
        Handle-Error "备份文件不存在: $File"
    }
    
    # 检查文件扩展名
    $ext = [System.IO.Path]::GetExtension($File).ToLower()
    if ($ext -ne ".zip") {
        Handle-Error "不支持的文件格式: $ext (仅支持 .zip)"
    }
    
    # 尝试打开压缩文件
    try {
        Add-Type -AssemblyName System.IO.Compression.FileSystem
        $zip = [System.IO.Compression.ZipFile]::OpenRead($File)
        $entries = $zip.Entries
        $hasManifest = $entries | Where-Object { $_.Name -eq "manifest.json" }
        $zip.Dispose()
        
        if (!$hasManifest) {
            Write-Log "警告: 备份文件缺少清单文件" -Level "WARN"
        }
        
        Write-Log "备份文件验证通过"
        return $true
    }
    catch {
        Handle-Error "备份文件验证失败: $($_.Exception.Message)"
        return $false
    }
}

# 读取备份清单
function Read-BackupManifest {
    param([string]$ExtractPath)
    
    $manifestPath = Join-Path $ExtractPath "manifest.json"
    if (Test-Path $manifestPath) {
        $manifest = Get-Content -Path $manifestPath -Raw | ConvertFrom-Json
        return $manifest
    }
    return $null
}

# 提取备份
function Expand-Backup {
    param([string]$BackupFile, [string]$ExtractPath)
    
    Write-Log "提取备份文件..."
    
    try {
        if (Test-Path $ExtractPath) {
            Remove-Item -Path $ExtractPath -Recurse -Force
        }
        New-Item -ItemType Directory -Path $ExtractPath -Force | Out-Null
        
        Expand-Archive -Path $BackupFile -DestinationPath $ExtractPath -Force
        Write-Log "备份文件已提取到: $ExtractPath"
        return $true
    }
    catch {
        Handle-Error "提取备份失败: $($_.Exception.Message)"
        return $false
    }
}

# 停止相关服务
function Stop-RelatedServices {
    Write-Log "检查并停止相关服务..."
    
    # 检查Python进程
    $pythonProcesses = Get-Process -Name "python" -ErrorAction SilentlyContinue | 
        Where-Object { $_.CommandLine -like "* FormalMath*" -or $_.CommandLine -like "*uvicorn*" }
    
    if ($pythonProcesses) {
        Write-Log "发现正在运行的服务进程: $($pythonProcesses.Count)个"
        if (Confirm-Action "是否停止这些进程?") {
            foreach ($proc in $pythonProcesses) {
                try {
                    Stop-Process -Id $proc.Id -Force
                    Write-Log "已停止进程: PID $($proc.Id)"
                }
                catch {
                    Write-Log "停止进程失败: PID $($proc.Id)" -Level "WARN"
                }
            }
        }
    }
}

# 备份当前数据（恢复前）
function Backup-CurrentData {
    param([string]$BackupDir)
    
    Write-Log "备份当前数据（防止意外）..."
    $preRestoreBackup = Join-Path $BackupDir "pre_restore_$Timestamp"
    
    try {
        # 备份现有数据库
        $dbFiles = @(
            "$ProjectRoot\api\formalmath.db",
            "$ProjectRoot\evaluation-system\backend\*.db",
            "$ProjectRoot\cognitive-diagnosis\backend\*.db"
        )
        
        $backupCount = 0
        foreach ($pattern in $dbFiles) {
            $files = Get-ChildItem -Path $pattern -ErrorAction SilentlyContinue
            foreach ($file in $files) {
                $dest = Join-Path $preRestoreBackup $file.Name
                Copy-Item -Path $file.FullName -Destination $dest -Force
                $backupCount++
            }
        }
        
        Write-Log "已备份 $backupCount 个现有数据库文件到: $preRestoreBackup"
        return $preRestoreBackup
    }
    catch {
        Write-Log "备份当前数据失败: $($_.Exception.Message)" -Level "WARN"
        return $null
    }
}

# 恢复数据库
function Restore-Database {
    param([string]$ExtractPath)
    
    Write-Log "开始恢复数据库..."
    $dbSourceDir = Join-Path $ExtractPath "database"
    
    if (!(Test-Path $dbSourceDir)) {
        Write-Log "备份中没有数据库文件，跳过" -Level "WARN"
        return $true
    }
    
    $dbMappings = @{
        "formalmath.db" = "$ProjectRoot\api\formalmath.db"
    }
    
    $successCount = 0
    $skipCount = 0
    
    foreach ($file in Get-ChildItem -Path $dbSourceDir -Filter "*.db") {
        $sourcePath = $file.FullName
        $destPath = $dbMappings[$file.Name]
        
        if (!$destPath) {
            # 尝试从文件名推断目标位置
            $destPath = "$ProjectRoot\api\$($file.Name)"
        }
        
        try {
            if ($DryRun) {
                Write-Log "[DRY RUN] 将恢复: $sourcePath -> $destPath"
                $successCount++
            } else {
                $destDir = Split-Path $destPath -Parent
                if (!(Test-Path $destDir)) {
                    New-Item -ItemType Directory -Path $destDir -Force | Out-Null
                }
                Copy-Item -Path $sourcePath -Destination $destPath -Force
                Write-Log "已恢复数据库: $($file.Name)"
                $successCount++
            }
        }
        catch {
            Write-Log "恢复失败: $($file.Name) - $($_.Exception.Message)" -Level "ERROR"
        }
    }
    
    Write-Log "数据库恢复完成: 成功 $successCount, 跳过 $skipCount"
    return $successCount -gt 0
}

# 恢复配置文件
function Restore-ConfigFiles {
    param([string]$ExtractPath)
    
    Write-Log "开始恢复配置文件..."
    $configSourceDir = Join-Path $ExtractPath "config"
    
    if (!(Test-Path $configSourceDir)) {
        Write-Log "备份中没有配置文件，跳过" -Level "WARN"
        return $true
    }
    
    $successCount = 0
    
    # 遍历配置目录中的所有文件
    foreach ($file in Get-ChildItem -Path $configSourceDir -Recurse -File) {
        $relativePath = $file.FullName.Substring($configSourceDir.Length + 1)
        $destPath = Join-Path $ProjectRoot $relativePath
        
        try {
            if ($DryRun) {
                Write-Log "[DRY RUN] 将恢复配置: $relativePath"
                $successCount++
            } else {
                $destDir = Split-Path $destPath -Parent
                if (!(Test-Path $destDir)) {
                    New-Item -ItemType Directory -Path $destDir -Force | Out-Null
                }
                Copy-Item -Path $file.FullName -Destination $destPath -Force
                Write-Log "已恢复配置: $relativePath"
                $successCount++
            }
        }
        catch {
            Write-Log "配置恢复失败: $relativePath - $($_.Exception.Message)" -Level "ERROR"
        }
    }
    
    Write-Log "配置文件恢复完成: 成功 $successCount"
    return $successCount -ge 0
}

# 恢复数据目录
function Restore-DataDirectories {
    param([string]$ExtractPath)
    
    Write-Log "开始恢复数据目录..."
    $dataSourceDir = Join-Path $ExtractPath "data"
    
    if (!(Test-Path $dataSourceDir)) {
        Write-Log "备份中没有数据目录，跳过" -Level "WARN"
        return $true
    }
    
    $successCount = 0
    
    foreach ($dir in Get-ChildItem -Path $dataSourceDir -Directory) {
        # 找到对应的目标目录
        $targetDir = $null
        switch ($dir.Name) {
            "evaluation" { $targetDir = "$ProjectRoot\api\app\evaluation" }
            "database" { $targetDir = "$ProjectRoot\cognitive-diagnosis\backend\app\database" }
            "test-data" { $targetDir = "$ProjectRoot\testing\test-data" }
            default { $targetDir = "$ProjectRoot\$($dir.Name)" }
        }
        
        try {
            if ($DryRun) {
                Write-Log "[DRY RUN] 将恢复数据目录: $($dir.Name) -> $targetDir"
                $successCount++
            } else {
                if (Test-Path $targetDir) {
                    Remove-Item -Path $targetDir -Recurse -Force
                }
                Copy-Item -Path $dir.FullName -Destination $targetDir -Recurse -Force
                Write-Log "已恢复数据目录: $($dir.Name)"
                $successCount++
            }
        }
        catch {
            Write-Log "数据目录恢复失败: $($dir.Name) - $($_.Exception.Message)" -Level "ERROR"
        }
    }
    
    Write-Log "数据目录恢复完成: 成功 $successCount"
    return $successCount -ge 0
}

# 恢复知识图谱
function Restore-KnowledgeGraph {
    param([string]$ExtractPath)
    
    Write-Log "开始恢复知识图谱数据..."
    $kgSourceDir = Join-Path $ExtractPath "knowledge_graph"
    
    if (!(Test-Path $kgSourceDir)) {
        Write-Log "备份中没有知识图谱数据，跳过" -Level "WARN"
        return $true
    }
    
    $successCount = 0
    $targetDir = "$ProjectRoot\.."  # 父目录
    
    foreach ($file in Get-ChildItem -Path $kgSourceDir -File) {
        $destPath = Join-Path $targetDir $file.Name
        
        try {
            if ($DryRun) {
                Write-Log "[DRY RUN] 将恢复知识图谱: $($file.Name)"
                $successCount++
            } else {
                Copy-Item -Path $file.FullName -Destination $destPath -Force
                Write-Log "已恢复知识图谱: $($file.Name)"
                $successCount++
            }
        }
        catch {
            Write-Log "知识图谱恢复失败: $($file.Name) - $($_.Exception.Message)" -Level "ERROR"
        }
    }
    
    Write-Log "知识图谱恢复完成: 成功 $successCount"
    return $successCount -ge 0
}

# 验证恢复结果
function Test-RestoreResult {
    Write-Log "验证恢复结果..."
    
    $checks = @{
        "数据库文件" = Test-Path "$ProjectRoot\api\formalmath.db"
        "核心配置" = Test-Path "$ProjectRoot\api\app\core\config.py"
        "项目根目录" = Test-Path $ProjectRoot
    }
    
    $allPassed = $true
    foreach ($check in $checks.GetEnumerator()) {
        $status = if ($check.Value) { "✓" } else { "✗" }
        Write-Log "验证 $status : $($check.Key)"
        if (!$check.Value) {
            $allPassed = $false
        }
    }
    
    return $allPassed
}

# 主执行流程
function Start-Restore {
    Write-Log "==========================================="
    Write-Log "FormalMath 恢复脚本 v$ScriptVersion"
    Write-Log "备份文件: $BackupFile"
    Write-Log "恢复类型: $RestoreType"
    Write-Log "恢复路径: $RestorePath"
    if ($DryRun) {
        Write-Log "模式: 仅演示 (Dry Run)"
    }
    Write-Log "==========================================="
    
    # 验证备份文件
    Test-BackupFile -File $BackupFile
    
    if ($VerifyOnly) {
        Write-Log "仅验证模式，不执行恢复"
        return $true
    }
    
    # 确认恢复
    if (!$DryRun -and !$Force) {
        if (!(Confirm-Action "警告: 恢复操作将覆盖现有数据。是否继续?")) {
            Write-Log "用户取消恢复操作"
            exit 0
        }
    }
    
    # 提取备份
    $extractPath = Join-Path $env:TEMP "formalmath_restore_$Timestamp"
    Expand-Backup -BackupFile $BackupFile -ExtractPath $extractPath
    
    # 读取备份清单
    $manifest = Read-BackupManifest -ExtractPath $extractPath
    if ($manifest) {
        Write-Log "备份信息:"
        Write-Log "  备份时间: $($manifest.timestamp)"
        Write-Log "  备份类型: $($manifest.backup_type)"
        Write-Log "  备份来源: $($manifest.hostname)"
    }
    
    # 停止服务
    if (!$DryRun) {
        Stop-RelatedServices
        
        # 备份当前数据
        $preRestoreBackup = Backup-CurrentData -BackupDir (Join-Path $ProjectRoot "backup\archive")
    }
    
    $allSuccess = $true
    
    # 根据恢复类型执行相应恢复
    switch ($RestoreType) {
        "full" {
            $allSuccess = $allSuccess -and (Restore-Database -ExtractPath $extractPath)
            $allSuccess = $allSuccess -and (Restore-ConfigFiles -ExtractPath $extractPath)
            $allSuccess = $allSuccess -and (Restore-DataDirectories -ExtractPath $extractPath)
            $allSuccess = $allSuccess -and (Restore-KnowledgeGraph -ExtractPath $extractPath)
        }
        "db" {
            $allSuccess = $allSuccess -and (Restore-Database -ExtractPath $extractPath)
        }
        "config" {
            $allSuccess = $allSuccess -and (Restore-ConfigFiles -ExtractPath $extractPath)
        }
        "data" {
            $allSuccess = $allSuccess -and (Restore-DataDirectories -ExtractPath $extractPath)
        }
    }
    
    # 验证恢复结果
    if (!$DryRun) {
        $verifySuccess = Test-RestoreResult
        if (!$verifySuccess) {
            Write-Log "恢复验证失败，请检查日志" -Level "ERROR"
            $allSuccess = $false
        }
    }
    
    # 清理临时目录
    Remove-Item -Path $extractPath -Recurse -Force -ErrorAction SilentlyContinue
    
    # 恢复结果
    Write-Log "==========================================="
    if ($allSuccess) {
        Write-Log "恢复成功完成!"
        if (!$DryRun -and $preRestoreBackup) {
            Write-Log "恢复前备份保存在: $preRestoreBackup"
        }
    } else {
        Write-Log "恢复完成，但存在一些问题" -Level "WARN"
    }
    Write-Log "==========================================="
    
    return $allSuccess
}

# 执行恢复
try {
    $result = Start-Restore
    exit ($result ? 0 : 1)
}
catch {
    Handle-Error "恢复过程中发生错误: $($_.Exception.Message)"
}
