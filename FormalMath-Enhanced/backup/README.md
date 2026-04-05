---
title: FormalMath 数据备份与恢复系统
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath 数据备份与恢复系统

## 系统概述

本系统为 FormalMath 项目提供完善的数据备份与恢复机制，支持自动备份、手动备份、增量备份和灾难恢复。

## 快速开始

### 1. 执行完整备份

```powershell
cd G:\_src\FormalMath\FormalMath-Enhanced\backup
.\scripts\backup.ps1 -BackupType full
```

### 2. 验证备份

```powershell
.\scripts\verify_backup.ps1 -Detailed
```

### 3. 执行恢复

```powershell
.\scripts\restore.ps1 -BackupFile "backup_full_20250401_120000.zip" -Force
```

## 目录结构

```
backup/
├── README.md                    # 本文件
├── scripts/                     # 备份脚本目录
│   ├── backup.ps1              # 主备份脚本
│   ├── restore.ps1             # 恢复脚本
│   └── verify_backup.ps1       # 验证脚本
├── docs/                        # 文档目录
│   ├── 备份配置指南.md          # 配置自动备份
│   ├── 恢复流程文档.md          # 数据恢复步骤
│   └── 灾难恢复计划.md          # 灾难恢复流程
├── archive/                     # 备份存储目录
└── logs/                        # 日志目录
```

## 功能特性

### 备份功能

- ✅ **完整备份**: 数据库、配置、数据目录、知识图谱、Lean4代码
- ✅ **增量备份**: 仅备份最近修改的文件
- ✅ **自动压缩**: 使用 ZIP 压缩节省空间
- ✅ **自动验证**: 备份后自动验证完整性
- ✅ **保留策略**: 自动清理过期备份
- ✅ **详细日志**: 记录所有操作日志

### 恢复功能

- ✅ **完整恢复**: 恢复所有数据类型
- ✅ **选择性恢复**: 仅恢复数据库/配置/数据
- ✅ **预恢复备份**: 自动备份当前数据
- ✅ **验证模式**: 仅验证不恢复
- ✅ **演示模式**: 显示操作但不执行

### 验证功能

- ✅ **完整性检查**: 验证备份文件结构
- ✅ **可恢复性测试**: 测试解压和数据可读性
- ✅ **批量验证**: 验证所有备份文件
- ✅ **详细报告**: 生成验证报告

## 备份类型

| 类型 | 说明 | 保留期建议 |
|------|------|-----------|
| full | 完整备份所有数据 | 30天 |
| db | 仅数据库文件 | 7天 |
| config | 仅配置文件 | 90天 |
| incremental | 最近修改的文件 | 7天 |

## 使用示例

### 手动备份

```powershell
# 完整备份
.\scripts\backup.ps1 -BackupType full

# 仅备份数据库
.\scripts\backup.ps1 -BackupType db

# 备份不压缩
.\scripts\backup.ps1 -BackupType full -Compress:$false

# 指定保留天数
.\scripts\backup.ps1 -BackupType full -RetentionDays 60
```

### 手动恢复

```powershell
# 完整恢复（有确认提示）
.\scripts\restore.ps1 -BackupFile "backup_full_20250401_120000.zip"

# 强制恢复（无确认提示）
.\scripts\restore.ps1 -BackupFile "backup_full_20250401_120000.zip" -Force

# 仅恢复数据库
.\scripts\restore.ps1 -BackupFile "backup_full_20250401_120000.zip" -RestoreType db

# 仅验证备份
.\scripts\restore.ps1 -BackupFile "backup_full_20250401_120000.zip" -VerifyOnly

# 演示模式
.\scripts\restore.ps1 -BackupFile "backup_full_20250401_120000.zip" -DryRun
```

### 验证备份

```powershell
# 验证最新备份
.\scripts\verify_backup.ps1

# 验证指定备份
.\scripts\verify_backup.ps1 -BackupFile "backup_full_20250401_120000.zip"

# 验证所有备份
.\scripts\verify_backup.ps1 -CheckAll

# 详细验证
.\scripts\verify_backup.ps1 -Detailed
```

## 自动备份配置

### Windows 任务计划程序

#### 每日完整备份 (02:00)

```powershell
$action = New-ScheduledTaskAction `
    -Execute "powershell.exe" `
    -Argument '-ExecutionPolicy Bypass -File "G:\_src\FormalMath\FormalMath-Enhanced\backup\scripts\backup.ps1" -BackupType full -RetentionDays 30'

$trigger = New-ScheduledTaskTrigger -Daily -At "02:00"

Register-ScheduledTask `
    -TaskName "FormalMath Full Backup" `
    -Action $action `
    -Trigger $trigger `
    -Description "FormalMath 系统每日完整备份"
```

#### 每小时数据库备份

```powershell
$action = New-ScheduledTaskAction `
    -Execute "powershell.exe" `
    -Argument '-ExecutionPolicy Bypass -File "G:\_src\FormalMath\FormalMath-Enhanced\backup\scripts\backup.ps1" -BackupType db -RetentionDays 7'

$trigger = New-ScheduledTaskTrigger `
    -Once -At (Get-Date) `
    -RepetitionInterval (New-TimeSpan -Hours 1) `
    -RepetitionDuration (New-TimeSpan -Days 365)

Register-ScheduledTask `
    -TaskName "FormalMath DB Backup" `
    -Action $action `
    -Trigger $trigger
```

详细配置说明参见 [备份配置指南](docs/备份配置指南.md)

## 灾难恢复

### 恢复时间目标 (RTO)

- **P1 灾难**: 4小时内恢复
- **P2 灾难**: 8小时内恢复
- **P3 灾难**: 24小时内恢复

### 恢复点目标 (RPO)

- **数据丢失**: 最大1小时

### 紧急恢复步骤

```
1. 评估灾难等级 (P1/P2/P3)
2. 联系恢复团队
3. 停止受影响服务
4. 定位最新备份: Get-ChildItem archive\backup_*.zip | Sort-Object LastWriteTime -Descending | Select-Object -First 1
5. 执行恢复: .\scripts\restore.ps1 -BackupFile "<file>" -Force
6. 验证恢复结果
7. 恢复服务
8. 监控运行状态
```

详细流程参见 [灾难恢复计划](docs/灾难恢复计划.md)

## 监控与维护

### 检查最近备份

```powershell
Get-ChildItem -Path "archive" -Filter "backup_*.zip" |
    Sort-Object LastWriteTime -Descending |
    Select-Object -First 5 |
    Format-Table Name, LastWriteTime, @{N="Size(MB)";E={[math]::Round($_.Length/1MB,2)}}
```

### 检查磁盘空间

```powershell
Get-PSDrive G | Select-Object Used, Free, @{N="Used%";E={[math]::Round(($_.Used/($_.Used+$_.Free))*100,2)}}
```

### 查看备份日志

```powershell
Get-Content -Path "logs\backup_$(Get-Date -Format 'yyyyMMdd')*.log" -Tail 50
```

## 故障排除

### 备份失败

1. 检查日志文件: `logs\backup_*.log`
2. 检查磁盘空间
3. 检查文件权限
4. 确认 PowerShell 执行策略

### 恢复失败

1. 验证备份文件: `.\scripts\verify_backup.ps1 -BackupFile "<file>"`
2. 检查目标目录权限
3. 停止相关服务
4. 查看恢复日志: `logs\restore_*.log`

### 磁盘空间不足

```powershell
# 清理旧备份
Get-ChildItem -Path "archive" -Filter "backup_*.zip" |
    Where-Object { $_.LastWriteTime -lt (Get-Date).AddDays(-14) } |
    Remove-Item -Force
```

## 文档索引

| 文档 | 说明 |
|------|------|
| [备份配置指南](docs/备份配置指南.md) | 自动备份配置说明 |
| [恢复流程文档](docs/恢复流程文档.md) | 数据恢复操作步骤 |
| [灾难恢复计划](docs/灾难恢复计划.md) | 灾难恢复流程和预案 |

## 系统要求

- Windows PowerShell 5.1 或更高版本
- .NET Framework 4.5 或更高版本
- 足够的磁盘空间用于备份

## 安全建议

1. **访问控制**: 限制备份目录访问权限
2. **异地备份**: 定期同步到远程位置
3. **加密存储**: 敏感备份文件建议加密
4. **定期测试**: 每季度执行恢复测试

## 联系支持

- 系统管理员: [待填写]
- 开发团队: [待填写]
- 紧急热线: [待填写]

---

**版本**: 1.0.0  
**更新日期**: 2026-04-04
