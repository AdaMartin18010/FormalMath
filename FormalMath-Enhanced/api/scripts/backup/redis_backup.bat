@echo off
chcp 65001 >nul
:: =============================================================================
:: FormalMath API - Redis 备份脚本 (Windows)
:: 版本: 1.0.0
:: 最后更新: 2026-04-04
:: =============================================================================

setlocal EnableDelayedExpansion

:: 配置变量
set "BACKUP_BASE_DIR=C:\Backups\FormalMath\Redis"
set "LOG_DIR=C:\Logs\FormalMath\Backup"
set "TIMESTAMP=%date:~0,4%%date:~5,2%%date:~8,2%_%time:~0,2%%time:~3,2%%time:~6,2%"
set "TIMESTAMP=!TIMESTAMP: =0!"
set "DATE=%date:~0,4%%date:~5,2%%date:~8,2%"

:: Redis配置
set "REDIS_HOST=%REDIS_HOST:localhost%"
set "REDIS_PORT=%REDIS_PORT:6379%"
set "REDIS_PASSWORD=%REDIS_PASSWORD:%"

:: 备份保留策略
set "BACKUP_RETENTION_DAYS=%BACKUP_RETENTION_DAYS:14%"

:: 创建目录
if not exist "%BACKUP_BASE_DIR%\rdb" mkdir "%BACKUP_BASE_DIR%\rdb"
if not exist "%BACKUP_BASE_DIR%\aof" mkdir "%BACKUP_BASE_DIR%\aof"
if not exist "%LOG_DIR%" mkdir "%LOG_DIR%"

:: 日志函数
:log
    echo [%date% %time%] [%~1] %~2 >> "%LOG_DIR%\redis_backup_%DATE%.log"
    echo [%date% %time%] [%~1] %~2
    goto :eof

:: 检查Redis连接
:check_redis_connection
    redis-cli -h %REDIS_HOST% -p %REDIS_PORT% %REDIS_AUTH% ping | findstr "PONG" >nul
    if errorlevel 1 (
        call :log "ERROR" "无法连接到Redis服务器"
        exit /b 1
    )
    goto :eof

:: 备份Redis
:backup_redis
    call :log "INFO" "开始备份Redis..."
    
    set "BACKUP_DIR=%BACKUP_BASE_DIR%\rdb\%DATE%"
    if not exist "%BACKUP_DIR%" mkdir "%BACKUP_DIR%"
    
    :: 设置认证
    if not "%REDIS_PASSWORD%"=="" (
        set "REDIS_AUTH=-a %REDIS_PASSWORD%"
    ) else (
        set "REDIS_AUTH="
    )
    
    :: 触发BGSAVE
    call :log "INFO" "触发后台保存..."
    redis-cli -h %REDIS_HOST% -p %REDIS_PORT% %REDIS_AUTH% BGSAVE >nul 2>&1
    
    :: 等待保存完成
    timeout /t 5 /nobreak >nul
    
    :: 获取RDB文件路径
    for /f "tokens=*" %%a in ('redis-cli -h %REDIS_HOST% -p %REDIS_PORT% %REDIS_AUTH% CONFIG GET dir ^| findstr /V "dir"') do (
        set "REDIS_DIR=%%a"
    )
    
    for /f "tokens=*" %%a in ('redis-cli -h %REDIS_HOST% -p %REDIS_PORT% %REDIS_AUTH% CONFIG GET dbfilename ^| findstr /V "dbfilename"') do (
        set "REDIS_FILE=%%a"
    )
    
    set "SOURCE_RDB=!REDIS_DIR!\!REDIS_FILE!"
    set "TARGET_RDB=%BACKUP_DIR%\dump_%TIMESTAMP%.rdb"
    
    :: 复制RDB文件
    if exist "!SOURCE_RDB!" (
        copy "!SOURCE_RDB!" "!TARGET_RDB!" >nul
        powershell -Command "Compress-Archive -Path '!TARGET_RDB!' -DestinationPath '!TARGET_RDB!.zip' -Force"
        del "!TARGET_RDB!"
        call :log "INFO" "RDB备份完成: !TARGET_RDB!.zip"
    ) else (
        call :log "ERROR" "RDB文件不存在: !SOURCE_RDB!"
        exit /b 1
    )
    
    goto :eof

:: 清理过期备份
:cleanup_old_backups
    call :log "INFO" "清理过期备份..."
    forfiles /P "%BACKUP_BASE_DIR%\rdb" /D -%BACKUP_RETENTION_DAYS% /C "cmd /c rmdir /S /Q @path" 2>nul
    call :log "INFO" "清理完成"
    goto :eof

:: 显示备份状态
:show_status
    echo ========================================
    echo          Redis 备份状态
    echo ========================================
    echo 备份目录: %BACKUP_BASE_DIR%
    echo 日志目录: %LOG_DIR%
    echo.
    echo RDB备份:
    dir /O-D /B "%BACKUP_BASE_DIR%\rdb" 2>nul | head -5 || echo   无RDB备份
    echo.
    echo Redis服务器信息:
    redis-cli -h %REDIS_HOST% -p %REDIS_PORT% %REDIS_AUTH% INFO server 2>nul | findstr "redis_version redis_mode" || echo   无法连接
    goto :eof

:: 使用说明
:usage
    echo 使用方法: %~nx0 [命令]
    echo.
    echo 命令:
    echo   backup        执行备份
    echo   cleanup       清理过期备份
    echo   status        显示备份状态
    echo.
    echo 环境变量:
    echo   REDIS_HOST        Redis主机 (默认: localhost)
    echo   REDIS_PORT        Redis端口 (默认: 6379)
    echo   REDIS_PASSWORD    Redis密码
    goto :eof

:: 主程序
if "%~1"=="backup" (
    call :backup_redis
) else if "%~1"=="cleanup" (
    call :cleanup_old_backups
) else if "%~1"=="status" (
    call :show_status
) else if "%~1"=="-h" (
    call :usage
) else if "%~1"=="--help" (
    call :usage
) else (
    call :backup_redis
)

endlocal
