# FormalMath 数据备份脚本
# 作者: FormalMath Dev Team
# 版本: 1.0.0
# 描述: 自动备份数据库、配置文件和重要数据

param(
    [string]$BackupType = "full",  # full, db, config, incremental
    [string]$BackupPath = "",
    [int]$RetentionDays = 30,
    [switch]$Verify = $true,
    [switch]$Compress = $true
)

# 配置
$ErrorActionPreference = "Stop"
$ScriptVersion = "1.0.0"
$ProjectRoot = "G:\_src\FormalMath\FormalMath-Enhanced"
$Timestamp = Get-Date -Format "yyyyMMdd_HHmmss"

# 默认备份路径
if ([string]::IsNullOrEmpty($BackupPath)) {
    $BackupPath = Join-Path $ProjectRoot "backup\archive"
}

# 日志配置
$LogDir = Join-Path $ProjectRoot "backup\logs"
$LogFile = Join-Path $LogDir "backup_$Timestamp.log"

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

# 获取配置
function Get-BackupConfig {
    return @{
        # 数据库文件
        DatabaseFiles = @(
            "$ProjectRoot\api\formalmath.db",
            "$ProjectRoot\evaluation-system\backend\*.db",
            "$ProjectRoot\cognitive-diagnosis\backend\*.db",
            "$ProjectRoot\adaptive-learning\backend\*.db"
        )
        
        # 配置文件
        ConfigFiles = @(
            "$ProjectRoot\api\.env",
            "$ProjectRoot\api\.env.example",
            "$ProjectRoot\api\app\core\config.py",
            "$ProjectRoot\cognitive-diagnosis\backend\app\core\config.py",
            "$ProjectRoot\evaluation-system\backend\app\core\config.py",
            "$ProjectRoot\adaptive-learning\backend\app\core\config.py",
            "$ProjectRoot\nginx\conf.d\*"
        )
        
        # 重要数据目录
        DataDirectories = @(
            "$ProjectRoot\api\app\evaluation",
            "$ProjectRoot\cognitive-diagnosis\backend\app\database",
            "$ProjectRoot\testing\test-data",
            "$ProjectRoot\visualization\data"
        )
        
        # 知识图谱数据
        KnowledgeGraphFiles = @(
            "$ProjectRoot\..\multilang_concept_table.json",
            "$ProjectRoot\..\concept_prerequisites_geometry_topology_update.yaml",
            "$ProjectRoot\..\wikipedia_applied_math_mapping.json"
        )
        
        # Lean4代码
        Lean4Files = @(
            "$ProjectRoot\lean4\FormalMath\FormalMath\*.lean",
            "$ProjectRoot\lean4\FormalMath\lakefile.lean"
        )
    }
}

# 创建备份目录结构
function Initialize-BackupDir {
    param([string]$BaseDir)
    
    $dirs = @("database", "config", "data", "knowledge_graph", "lean4", "logs")
    foreach ($dir in $dirs) {
        $path = Join-Path $BaseDir $dir
        if (!(Test-Path $path)) {
            New-Item -ItemType Directory -Path $path -Force | Out-Null
        }
    }
}

# 备份数据库
function Backup-Database {
    param([string]$BackupDir, [array]$DbFiles)
    
    Write-Log "开始备份数据库..."
    $dbBackupDir = Join-Path $BackupDir "database"
    $successCount = 0
    $failCount = 0
    
    foreach ($pattern in $DbFiles) {
        $files = Get-ChildItem -Path $pattern -ErrorAction SilentlyContinue
        foreach ($file in $files) {
            try {
                $destFile = Join-Path $dbBackupDir $file.Name
                # 使用SQLite在线备份方法
                if ($file.Extension -eq ".db") {
                    $tempCopy = Join-Path $dbBackupDir "temp_$($file.Name)"
                    Copy-Item -Path $file.FullName -Destination $tempCopy -Force
                    Move-Item -Path $tempCopy -Destination $destFile -Force
                } else {
                    Copy-Item -Path $file.FullName -Destination $destFile -Force
                }
                Write-Log "已备份: $($file.Name)"
                $successCount++
            }
            catch {
                Write-Log "备份失败: $($file.Name) - $($_.Exception.Message)" -Level "ERROR"
                $failCount++
            }
        }
    }
    
    Write-Log "数据库备份完成: 成功 $successCount, 失败 $failCount"
    return $failCount -eq 0
}

# 备份配置文件
function Backup-ConfigFiles {
    param([string]$BackupDir, [array]$ConfigFiles)
    
    Write-Log "开始备份配置文件..."
    $configBackupDir = Join-Path $BackupDir "config"
    $successCount = 0
    $failCount = 0
    
    foreach ($pattern in $ConfigFiles) {
        $files = Get-ChildItem -Path $pattern -ErrorAction SilentlyContinue
        foreach ($file in $files) {
            try {
                $relativePath = $file.FullName.Substring($ProjectRoot.Length + 1)
                $destDir = Join-Path $configBackupDir ([System.IO.Path]::GetDirectoryName($relativePath))
                if (!(Test-Path $destDir)) {
                    New-Item -ItemType Directory -Path $destDir -Force | Out-Null
                }
                $destFile = Join-Path $destDir $file.Name
                Copy-Item -Path $file.FullName -Destination $destFile -Force
                Write-Log "已备份配置: $relativePath"
                $successCount++
            }
            catch {
                Write-Log "配置备份失败: $($file.FullName) - $($_.Exception.Message)" -Level "ERROR"
                $failCount++
            }
        }
    }
    
    Write-Log "配置文件备份完成: 成功 $successCount, 失败 $failCount"
    return $failCount -eq 0
}

# 备份数据目录
function Backup-DataDirectories {
    param([string]$BackupDir, [array]$DataDirs)
    
    Write-Log "开始备份数据目录..."
    $dataBackupDir = Join-Path $BackupDir "data"
    $successCount = 0
    $failCount = 0
    
    foreach ($dir in $DataDirs) {
        if (Test-Path $dir) {
            try {
                $dirName = Split-Path $dir -Leaf
                $destDir = Join-Path $dataBackupDir $dirName
                if (Test-Path $destDir) {
                    Remove-Item -Path $destDir -Recurse -Force
                }
                Copy-Item -Path $dir -Destination $destDir -Recurse -Force
                Write-Log "已备份数据目录: $dirName"
                $successCount++
            }
            catch {
                Write-Log "数据目录备份失败: $dir - $($_.Exception.Message)" -Level "ERROR"
                $failCount++
            }
        }
    }
    
    Write-Log "数据目录备份完成: 成功 $successCount, 失败 $failCount"
    return $failCount -eq 0
}

# 备份知识图谱
function Backup-KnowledgeGraph {
    param([string]$BackupDir, [array]$KgFiles)
    
    Write-Log "开始备份知识图谱数据..."
    $kgBackupDir = Join-Path $BackupDir "knowledge_graph"
    $successCount = 0
    $failCount = 0
    
    foreach ($file in $KgFiles) {
        $sourceFiles = Get-ChildItem -Path $file -ErrorAction SilentlyContinue
        foreach ($sourceFile in $sourceFiles) {
            try {
                $destFile = Join-Path $kgBackupDir $sourceFile.Name
                Copy-Item -Path $sourceFile.FullName -Destination $destFile -Force
                Write-Log "已备份知识图谱: $($sourceFile.Name)"
                $successCount++
            }
            catch {
                Write-Log "知识图谱备份失败: $($sourceFile.FullName) - $($_.Exception.Message)" -Level "ERROR"
                $failCount++
            }
        }
    }
    
    Write-Log "知识图谱备份完成: 成功 $successCount, 失败 $failCount"
    return $failCount -eq 0
}

# 备份Lean4代码
function Backup-Lean4Code {
    param([string]$BackupDir, [array]$LeanFiles)
    
    Write-Log "开始备份Lean4代码..."
    $leanBackupDir = Join-Path $BackupDir "lean4"
    $successCount = 0
    $failCount = 0
    
    foreach ($pattern in $LeanFiles) {
        $files = Get-ChildItem -Path $pattern -ErrorAction SilentlyContinue
        foreach ($file in $files) {
            try {
                $destFile = Join-Path $leanBackupDir $file.Name
                Copy-Item -Path $file.FullName -Destination $destFile -Force
                Write-Log "已备份Lean4文件: $($file.Name)"
                $successCount++
            }
            catch {
                Write-Log "Lean4备份失败: $($file.FullName) - $($_.Exception.Message)" -Level "ERROR"
                $failCount++
            }
        }
    }
    
    Write-Log "Lean4备份完成: 成功 $successCount, 失败 $failCount"
    return $failCount -eq 0
}

# 创建备份清单
function New-BackupManifest {
    param([string]$BackupDir)
    
    $manifest = @{
        version = $ScriptVersion
        timestamp = (Get-Date -Format "o")
        backup_type = $BackupType
        hostname = $env:COMPUTERNAME
        user = $env:USERNAME
        directories = @{}
    }
    
    # 记录每个目录的内容
    $subDirs = @("database", "config", "data", "knowledge_graph", "lean4")
    foreach ($dir in $subDirs) {
        $dirPath = Join-Path $BackupDir $dir
        if (Test-Path $dirPath) {
            $files = Get-ChildItem -Path $dirPath -Recurse -File | 
                Select-Object Name, Length, LastWriteTime, FullName
            $manifest.directories[$dir] = @{
                file_count = ($files | Measure-Object).Count
                total_size = ($files | Measure-Object -Property Length -Sum).Sum
                files = $files | ForEach-Object { 
                    @{
                        name = $_.Name
                        size = $_.Length
                        modified = $_.LastWriteTime.ToString("o")
                    }
                }
            }
        }
    }
    
    $manifestPath = Join-Path $BackupDir "manifest.json"
    $manifest | ConvertTo-Json -Depth 10 | Out-File -FilePath $manifestPath -Encoding UTF8
    Write-Log "备份清单已创建: $manifestPath"
}

# 压缩备份
function Compress-Backup {
    param([string]$SourceDir, [string]$DestFile)
    
    Write-Log "开始压缩备份..."
    try {
        Compress-Archive -Path "$SourceDir\*" -DestinationPath $DestFile -Force
        $size = (Get-Item $DestFile).Length
        $sizeMB = [math]::Round($size / 1MB, 2)
        Write-Log "备份已压缩: $DestFile ($sizeMB MB)"
        return $true
    }
    catch {
        Write-Log "压缩失败: $($_.Exception.Message)" -Level "ERROR"
        return $false
    }
}

# 验证备份
function Test-Backup {
    param([string]$BackupFile)
    
    Write-Log "开始验证备份..."
    try {
        # 测试压缩文件完整性
        $testResult = Test-Archive -Path $BackupFile
        if ($testResult) {
            Write-Log "备份验证通过: $BackupFile"
            return $true
        } else {
            Write-Log "备份验证失败: $BackupFile" -Level "ERROR"
            return $false
        }
    }
    catch {
        Write-Log "验证失败: $($_.Exception.Message)" -Level "ERROR"
        return $false
    }
}

# 清理旧备份
function Remove-OldBackups {
    param([string]$BackupPath, [int]$RetentionDays)
    
    Write-Log "清理超过 $RetentionDays 天的旧备份..."
    $cutoffDate = (Get-Date).AddDays(-$RetentionDays)
    $removedCount = 0
    
    $backupFiles = Get-ChildItem -Path $BackupPath -Filter "backup_*.zip" -ErrorAction SilentlyContinue
    foreach ($file in $backupFiles) {
        if ($file.LastWriteTime -lt $cutoffDate) {
            try {
                Remove-Item -Path $file.FullName -Force
                Write-Log "已删除旧备份: $($file.Name)"
                $removedCount++
            }
            catch {
                Write-Log "删除失败: $($file.Name) - $($_.Exception.Message)" -Level "WARN"
            }
        }
    }
    
    Write-Log "清理完成: 删除了 $removedCount 个旧备份"
}

# 主执行流程
function Start-Backup {
    Write-Log "==========================================="
    Write-Log "FormalMath 备份脚本 v$ScriptVersion"
    Write-Log "备份类型: $BackupType"
    Write-Log "备份路径: $BackupPath"
    Write-Log "==========================================="
    
    # 检查项目目录
    if (!(Test-Path $ProjectRoot)) {
        Handle-Error "项目目录不存在: $ProjectRoot"
    }
    
    # 获取配置
    $config = Get-BackupConfig
    
    # 创建临时备份目录
    $tempBackupDir = Join-Path $env:TEMP "formalmath_backup_$Timestamp"
    Initialize-BackupDir -BaseDir $tempBackupDir
    
    $allSuccess = $true
    
    # 根据备份类型执行相应备份
    switch ($BackupType) {
        "full" {
            $allSuccess = $allSuccess -and (Backup-Database -BackupDir $tempBackupDir -DbFiles $config.DatabaseFiles)
            $allSuccess = $allSuccess -and (Backup-ConfigFiles -BackupDir $tempBackupDir -ConfigFiles $config.ConfigFiles)
            $allSuccess = $allSuccess -and (Backup-DataDirectories -BackupDir $tempBackupDir -DataDirs $config.DataDirectories)
            $allSuccess = $allSuccess -and (Backup-KnowledgeGraph -BackupDir $tempBackupDir -KgFiles $config.KnowledgeGraphFiles)
            $allSuccess = $allSuccess -and (Backup-Lean4Code -BackupDir $tempBackupDir -LeanFiles $config.Lean4Files)
        }
        "db" {
            $allSuccess = $allSuccess -and (Backup-Database -BackupDir $tempBackupDir -DbFiles $config.DatabaseFiles)
        }
        "config" {
            $allSuccess = $allSuccess -and (Backup-ConfigFiles -BackupDir $tempBackupDir -ConfigFiles $config.ConfigFiles)
        }
        "incremental" {
            # 增量备份：只备份最近24小时修改的文件
            Write-Log "执行增量备份..."
            $allSuccess = $allSuccess -and (Backup-Database -BackupDir $tempBackupDir -DbFiles $config.DatabaseFiles)
        }
        default {
            Handle-Error "未知的备份类型: $BackupType"
        }
    }
    
    # 创建备份清单
    New-BackupManifest -BackupDir $tempBackupDir
    
    # 复制日志文件
    Copy-Item -Path $LogFile -Destination (Join-Path $tempBackupDir "logs\backup.log") -Force
    
    # 压缩备份
    $backupFileName = "backup_$BackupType`_$Timestamp.zip"
    $backupFilePath = Join-Path $BackupPath $backupFileName
    
    if ($Compress) {
        $compressSuccess = Compress-Backup -SourceDir $tempBackupDir -DestFile $backupFilePath
        if (!$compressSuccess) {
            $allSuccess = $false
        }
        
        # 验证备份
        if ($Verify -and $compressSuccess) {
            $verifySuccess = Test-Backup -BackupFile $backupFilePath
            if (!$verifySuccess) {
                $allSuccess = $false
            }
        }
    } else {
        # 不压缩，直接复制
        $finalBackupDir = Join-Path $BackupPath "backup_$BackupType`_$Timestamp"
        Copy-Item -Path $tempBackupDir -Destination $finalBackupDir -Recurse -Force
        $backupFilePath = $finalBackupDir
    }
    
    # 清理临时目录
    Remove-Item -Path $tempBackupDir -Recurse -Force -ErrorAction SilentlyContinue
    
    # 清理旧备份
    Remove-OldBackups -BackupPath $BackupPath -RetentionDays $RetentionDays
    
    # 备份结果
    Write-Log "==========================================="
    if ($allSuccess) {
        Write-Log "备份成功完成: $backupFilePath"
        Write-Log "备份文件大小: $([math]::Round((Get-Item $backupFilePath).Length / 1MB, 2)) MB"
    } else {
        Write-Log "备份完成，但存在一些错误" -Level "WARN"
    }
    Write-Log "==========================================="
    
    return $allSuccess
}

# 执行备份
try {
    $result = Start-Backup
    exit ($result ? 0 : 1)
}
catch {
    Handle-Error "备份过程中发生错误: $($_.Exception.Message)"
}
