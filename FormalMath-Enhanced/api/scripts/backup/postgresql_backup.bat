@echo off
chcp 65001 >nul
:: =============================================================================
:: FormalMath API - PostgreSQL 备份脚本 (Windows)
:: 版本: 1.0.0
:: 最后更新: 2026-04-04
:: =============================================================================

setlocal EnableDelayedExpansion

:: 配置变量
set "BACKUP_BASE_DIR=C:\Backups\FormalMath\PostgreSQL"
set "LOG_DIR=C:\Logs\FormalMath\Backup"
set "TIMESTAMP=%date:~0,4%%date:~5,2%%date:~8,2%_%time:~0,2%%time:~3,2%%time:~6,2%"
set "TIMESTAMP=!TIMESTAMP: =0!"
set "DATE=%date:~0,4%%date:~5,2%%date:~8,2%"

:: 数据库配置
set "DB_HOST=%DB_HOST:localhost%"
set "DB_PORT=%DB_PORT:5432%"
set "DB_NAME=%DB_NAME:formalmath%"
set "DB_USER=%DB_USER:postgres%"
set "DB_PASSWORD=%DB_PASSWORD:%"

:: 备份保留策略
set "FULL_BACKUP_RETENTION_DAYS=%FULL_BACKUP_RETENTION_DAYS:30%"

:: 创建目录
if not exist "%BACKUP_BASE_DIR%\full" mkdir "%BACKUP_BASE_DIR%\full"
if not exist "%BACKUP_BASE_DIR%\incremental" mkdir "%BACKUP_BASE_DIR%\incremental"
if not exist "%LOG_DIR%" mkdir "%LOG_DIR%"

:: 日志函数
:log
    echo [%date% %time%] [%~1] %~2 >> "%LOG_DIR%\backup_%DATE%.log"
    echo [%date% %time%] [%~1] %~2
    goto :eof

:: 检查依赖
:check_dependencies
    where pg_dump >nul 2>&1
    if errorlevel 1 (
        call :log "ERROR" "pg_dump未找到，请安装PostgreSQL客户端"
        exit /b 1
    )
    goto :eof

:: 全量备份
:full_backup
    call :log "INFO" "开始全量备份..."
    
    set "BACKUP_DIR=%BACKUP_BASE_DIR%\full\%DATE%"
    set "BACKUP_FILE=%BACKUP_DIR%\formalmath_%TIMESTAMP%.sql"
    
    if not exist "%BACKUP_DIR%" mkdir "%BACKUP_DIR%"
    
    :: 设置密码环境变量
    set PGPASSWORD=%DB_PASSWORD%
    
    :: 执行备份
    call :log "INFO" "备份数据库: %DB_NAME%"
    pg_dump -h %DB_HOST% -p %DB_PORT% -U %DB_USER% -Fc --verbose --blobs --no-owner --no-privileges "%DB_NAME%" > "%BACKUP_FILE%" 2>> "%LOG_DIR%\backup_%DATE%.log"
    
    if errorlevel 1 (
        call :log "ERROR" "备份失败"
        exit /b 1
    )
    
    :: 压缩备份
    call :log "INFO" "压缩备份文件..."
    powershell -Command "Compress-Archive -Path '%BACKUP_FILE%' -DestinationPath '%BACKUP_FILE%.zip' -Force"
    del "%BACKUP_FILE%"
    
    :: 计算文件大小
    for %%F in ("%BACKUP_FILE%.zip") do set "SIZE=%%~zF"
    call :log "INFO" "全量备份完成: %BACKUP_FILE%.zip (大小: %SIZE% 字节)"
    
    goto :eof

:: 清理过期备份
:cleanup_old_backups
    call :log "INFO" "清理过期备份..."
    
    forfiles /P "%BACKUP_BASE_DIR%\full" /S /D -%FULL_BACKUP_RETENTION_DAYS% /C "cmd /c rmdir /S /Q @path" 2>nul
    
    call :log "INFO" "清理完成"
    goto :eof

:: 显示备份状态
:show_status
    echo ========================================
    echo       PostgreSQL 备份状态
    echo ========================================
    echo 备份目录: %BACKUP_BASE_DIR%
    echo 日志目录: %LOG_DIR%
    echo.
    echo 全量备份:
    dir /O-D /B "%BACKUP_BASE_DIR%\full" 2>nul | head -5 || echo   无全量备份
    echo.
    echo 磁盘使用情况:
    wmic logicaldisk where "DeviceID='%BACKUP_BASE_DIR:~0,2%'" get FreeSpace,Size /value 2>nul
    goto :eof

:: 使用说明
:usage
    echo 使用方法: %~nx0 [命令]
    echo.
    echo 命令:
    echo   full          执行全量备份
    echo   cleanup       清理过期备份
    echo   status        显示备份状态
    echo.
    echo 环境变量:
    echo   DB_HOST       数据库主机 (默认: localhost)
    echo   DB_PORT       数据库端口 (默认: 5432)
    echo   DB_NAME       数据库名称 (默认: formalmath)
    echo   DB_USER       数据库用户 (默认: postgres)
    echo   DB_PASSWORD   数据库密码
    goto :eof

:: 主程序
if "%~1"=="full" (
    call :check_dependencies
    call :full_backup
) else if "%~1"=="cleanup" (
    call :cleanup_old_backups
) else if "%~1"=="status" (
    call :show_status
) else if "%~1"=="-h" (
    call :usage
) else if "%~1"=="--help" (
    call :usage
) else (
    call :usage
    exit /b 1
)

endlocal
