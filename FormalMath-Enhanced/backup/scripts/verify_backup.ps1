# FormalMath 备份验证脚本
# 作者: FormalMath Dev Team
# 版本: 1.0.0
# 描述: 验证备份文件的完整性和可恢复性

param(
    [Parameter(Mandatory=$false)]
    [string]$BackupFile,
    
    [string]$BackupPath = "",
    [switch]$CheckAll = $false,
    [switch]$Detailed = $false
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
$LogFile = Join-Path $LogDir "verify_$Timestamp.log"

# 确保日志目录存在
if (!(Test-Path $LogDir)) {
    New-Item -ItemType Directory -Path $LogDir -Force | Out-Null
}

# 日志函数
function Write-Log {
    param([string]$Message, [string]$Level = "INFO", [switch]$NoConsole)
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logEntry = "[$timestamp] [$Level] $Message"
    if (!$NoConsole) {
        switch ($Level) {
            "ERROR" { Write-Host $logEntry -ForegroundColor Red }
            "WARN" { Write-Host $logEntry -ForegroundColor Yellow }
            "SUCCESS" { Write-Host $logEntry -ForegroundColor Green }
            default { Write-Host $logEntry }
        }
    }
    Add-Content -Path $LogFile -Value $logEntry
}

# 错误处理
function Handle-Error {
    param([string]$Message)
    Write-Log -Message $Message -Level "ERROR"
    exit 1
}

# 验证单个备份文件
function Test-BackupIntegrity {
    param([string]$File)
    
    $result = @{
        FileName = [System.IO.Path]::GetFileName($File)
        FilePath = $File
        FileSize = 0
        FileSizeMB = 0
        CreatedAt = $null
        ModifiedAt = $null
        IsValid = $false
        HasManifest = $false
        ManifestValid = $false
        DatabaseCount = 0
        ConfigCount = 0
        DataDirCount = 0
        TotalFiles = 0
        Errors = @()
        Warnings = @()
    }
    
    try {
        # 基本文件检查
        if (!(Test-Path $File)) {
            $result.Errors += "文件不存在"
            return $result
        }
        
        $fileInfo = Get-Item $File
        $result.FileSize = $fileInfo.Length
        $result.FileSizeMB = [math]::Round($fileInfo.Length / 1MB, 2)
        $result.CreatedAt = $fileInfo.CreationTime.ToString("o")
        $result.ModifiedAt = $fileInfo.LastWriteTime.ToString("o")
        
        # 检查文件扩展名
        $ext = [System.IO.Path]::GetExtension($File).ToLower()
        if ($ext -ne ".zip") {
            $result.Errors += "不支持的文件格式: $ext"
            return $result
        }
        
        # 打开压缩文件
        Add-Type -AssemblyName System.IO.Compression.FileSystem
        $zip = [System.IO.Compression.ZipFile]::OpenRead($File)
        
        try {
            $result.TotalFiles = $zip.Entries.Count
            
            # 检查关键文件
            $manifestEntry = $zip.Entries | Where-Object { $_.Name -eq "manifest.json" }
            $result.HasManifest = ($manifestEntry -ne $null)
            
            if ($result.HasManifest) {
                # 尝试读取清单
                try {
                    $stream = $manifestEntry.Open()
                    $reader = New-Object System.IO.StreamReader($stream)
                    $manifestContent = $reader.ReadToEnd()
                    $reader.Close()
                    $stream.Close()
                    
                    $manifest = $manifestContent | ConvertFrom-Json
                    $result.ManifestValid = $true
                    
                    # 统计各类文件
                    if ($manifest.directories) {
                        if ($manifest.directories.database) {
                            $result.DatabaseCount = $manifest.directories.database.file_count
                        }
                        if ($manifest.directories.config) {
                            $result.ConfigCount = $manifest.directories.config.file_count
                        }
                        if ($manifest.directories.data) {
                            $result.DataDirCount = $manifest.directories.data.file_count
                        }
                    }
                }
                catch {
                    $result.Errors += "清单文件解析失败: $($_.Exception.Message)"
                    $result.ManifestValid = $false
                }
            } else {
                $result.Warnings += "缺少清单文件"
            }
            
            # 检查关键目录结构
            $expectedDirs = @("database", "config", "data", "knowledge_graph")
            foreach ($dir in $expectedDirs) {
                $dirEntries = $zip.Entries | Where-Object { $_.FullName -like "$dir/*" }
                if (($dirEntries | Measure-Object).Count -eq 0) {
                    $result.Warnings += "缺少目录: $dir"
                }
            }
            
            $result.IsValid = $true
        }
        finally {
            $zip.Dispose()
        }
    }
    catch {
        $result.Errors += "验证失败: $($_.Exception.Message)"
        $result.IsValid = $false
    }
    
    return $result
}

# 测试备份可恢复性
function Test-BackupRestorability {
    param([string]$File)
    
    Write-Log "测试备份可恢复性: $([System.IO.Path]::GetFileName($File))"
    
    $tempExtractPath = Join-Path $env:TEMP "formalmath_verify_$([Guid]::NewGuid().ToString().Substring(0,8))"
    $result = @{
        CanExtract = $false
        HasDatabase = $false
        HasConfig = $false
        HasData = $false
        ManifestReadable = $false
        Errors = @()
    }
    
    try {
        # 尝试解压
        Expand-Archive -Path $File -DestinationPath $tempExtractPath -Force
        $result.CanExtract = $true
        
        # 检查关键文件
        $result.HasDatabase = Test-Path (Join-Path $tempExtractPath "database\*.db")
        $result.HasConfig = Test-Path (Join-Path $tempExtractPath "config")
        $result.HasData = Test-Path (Join-Path $tempExtractPath "data")
        
        # 检查清单
        $manifestPath = Join-Path $tempExtractPath "manifest.json"
        if (Test-Path $manifestPath) {
            try {
                $manifest = Get-Content -Path $manifestPath -Raw | ConvertFrom-Json
                $result.ManifestReadable = $true
            }
            catch {
                $result.Errors += "清单文件无法读取"
            }
        }
    }
    catch {
        $result.Errors += "解压失败: $($_.Exception.Message)"
    }
    finally {
        # 清理临时目录
        if (Test-Path $tempExtractPath) {
            Remove-Item -Path $tempExtractPath -Recurse -Force -ErrorAction SilentlyContinue
        }
    }
    
    return $result
}

# 生成验证报告
function New-VerificationReport {
    param([array]$Results)
    
    $reportPath = Join-Path $BackupPath "verification_report_$Timestamp.json"
    $report = @{
        timestamp = (Get-Date -Format "o")
        script_version = $ScriptVersion
        total_backups = $Results.Count
        valid_backups = ($Results | Where-Object { $_.IsValid }).Count
        invalid_backups = ($Results | Where-Object { !$_.IsValid }).Count
        backups = $Results
    }
    
    $report | ConvertTo-Json -Depth 10 | Out-File -FilePath $reportPath -Encoding UTF8
    Write-Log "验证报告已保存: $reportPath"
    
    return $reportPath
}

# 显示验证结果
function Show-VerificationResult {
    param([hashtable]$Result, [switch]$Detailed)
    
    Write-Log "==========================================="
    Write-Log "备份文件: $($Result.FileName)"
    Write-Log "==========================================="
    Write-Log "文件大小: $($Result.FileSizeMB) MB"
    Write-Log "创建时间: $($Result.CreatedAt)"
    Write-Log "修改时间: $($Result.ModifiedAt)"
    Write-Log "总文件数: $($Result.TotalFiles)"
    
    $validStatus = if ($Result.IsValid) { "✓ 有效" } else { "✗ 无效" }
    Write-Log "有效性: $validStatus" -Level $(if ($Result.IsValid) { "SUCCESS" } else { "ERROR" })
    
    Write-Log "清单文件: $(if ($Result.HasManifest) { "✓ 存在" } else { "✗ 缺失" })"
    if ($Result.HasManifest) {
        Write-Log "清单有效: $(if ($Result.ManifestValid) { "✓ 是" } else { "✗ 否" })"
    }
    
    Write-Log "数据库文件: $($Result.DatabaseCount)"
    Write-Log "配置文件: $($Result.ConfigCount)"
    Write-Log "数据文件: $($Result.DataDirCount)"
    
    if ($Detailed) {
        if ($Result.Warnings.Count -gt 0) {
            Write-Log "警告:" -Level "WARN"
            foreach ($warning in $Result.Warnings) {
                Write-Log "  - $warning" -Level "WARN"
            }
        }
        
        if ($Result.Errors.Count -gt 0) {
            Write-Log "错误:" -Level "ERROR"
            foreach ($error in $Result.Errors) {
                Write-Log "  - $error" -Level "ERROR"
            }
        }
    }
}

# 主执行流程
function Start-Verification {
    Write-Log "==========================================="
    Write-Log "FormalMath 备份验证脚本 v$ScriptVersion"
    Write-Log "==========================================="
    
    $results = @()
    
    if ($CheckAll) {
        # 验证所有备份
        Write-Log "验证所有备份文件..."
        $backupFiles = Get-ChildItem -Path $BackupPath -Filter "backup_*.zip" | 
            Sort-Object LastWriteTime -Descending
        
        if ($backupFiles.Count -eq 0) {
            Write-Log "未找到备份文件" -Level "WARN"
            return
        }
        
        Write-Log "找到 $($backupFiles.Count) 个备份文件"
        
        foreach ($file in $backupFiles) {
            Write-Log "验证中: $($file.Name)..."
            $result = Test-BackupIntegrity -File $file.FullName
            
            if ($Detailed) {
                $restoreTest = Test-BackupRestorability -File $file.FullName
                $result | Add-Member -NotePropertyName "Restorability" -NotePropertyValue $restoreTest
            }
            
            $results += $result
            Show-VerificationResult -Result $result -Detailed:$Detailed
        }
    } 
    elseif ($BackupFile) {
        # 验证指定备份
        if (!(Test-Path $BackupFile)) {
            # 尝试在备份目录中查找
            $fullPath = Join-Path $BackupPath $BackupFile
            if (Test-Path $fullPath) {
                $BackupFile = $fullPath
            } else {
                Handle-Error "备份文件不存在: $BackupFile"
            }
        }
        
        Write-Log "验证指定备份: $BackupFile"
        $result = Test-BackupIntegrity -File $BackupFile
        
        if ($Detailed) {
            $restoreTest = Test-BackupRestorability -File $BackupFile
            $result | Add-Member -NotePropertyName "Restorability" -NotePropertyValue $restoreTest
        }
        
        $results += $result
        Show-VerificationResult -Result $result -Detailed:$Detailed
    } 
    else {
        # 验证最新的备份
        Write-Log "验证最新备份..."
        $latestBackup = Get-ChildItem -Path $BackupPath -Filter "backup_*.zip" | 
            Sort-Object LastWriteTime -Descending | 
            Select-Object -First 1
        
        if (!$latestBackup) {
            Handle-Error "未找到备份文件"
        }
        
        Write-Log "最新备份: $($latestBackup.Name)"
        $result = Test-BackupIntegrity -File $latestBackup.FullName
        
        if ($Detailed) {
            $restoreTest = Test-BackupRestorability -File $latestBackup.FullName
            $result | Add-Member -NotePropertyName "Restorability" -NotePropertyValue $restoreTest
        }
        
        $results += $result
        Show-VerificationResult -Result $result -Detailed:$Detailed
    }
    
    # 生成报告
    $reportPath = New-VerificationReport -Results $results
    
    # 汇总
    Write-Log "==========================================="
    Write-Log "验证汇总"
    Write-Log "==========================================="
    Write-Log "总备份数: $($results.Count)"
    Write-Log "有效备份: $(($results | Where-Object { $_.IsValid }).Count)" -Level "SUCCESS"
    Write-Log "无效备份: $(($results | Where-Object { !$_.IsValid }).Count)" -Level $(if (($results | Where-Object { !$_.IsValid }).Count -gt 0) { "ERROR" } else { "INFO" })
    Write-Log "==========================================="
}

# 执行验证
try {
    Start-Verification
}
catch {
    Handle-Error "验证过程中发生错误: $($_.Exception.Message)"
}
