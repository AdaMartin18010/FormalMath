#!/bin/bash
# ============================================
# FormalMath - 日志轮转和清理脚本
# 支持Docker日志、应用日志、Nginx日志管理
# ============================================

set -euo pipefail

# 配置
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
LOG_DIR="${PROJECT_ROOT}/logs"
ARCHIVE_DIR="${LOG_DIR}/archive"
DOCKER_LOG_MAX_SIZE="100m"
DOCKER_LOG_MAX_FILE="10"
RETENTION_DAYS=30

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# 日志函数
log() {
    local level=$1
    shift
    local message="$*"
    local timestamp=$(date '+%Y-%m-%d %H:%M:%S')
    echo "[$timestamp] [$level] $message"
}

info() { log "INFO" "$@"; }
warn() { log "WARN" "$@"; }
error() { log "ERROR" "$@"; }
success() { log "SUCCESS" "$@"; }

# 显示帮助
show_help() {
    cat << EOF
FormalMath 日志管理脚本

用法: $0 [选项] [命令]

命令:
    rotate      轮转日志文件
    clean       清理过期日志
    archive     归档旧日志
    size        查看日志大小
    docker      配置Docker日志限制
    compress    压缩旧日志
    report      生成日志报告

选项:
    -d, --days          保留天数 (默认: 30)
    -s, --size          大小限制 (默认: 100m)
    -f, --force         强制执行
    -h, --help          显示帮助

示例:
    $0 rotate
    $0 clean -d 7
    $0 archive
    $0 size
EOF
}

# 初始化目录结构
init_directories() {
    mkdir -p "$LOG_DIR" "$ARCHIVE_DIR"
    mkdir -p "$LOG_DIR"/{nginx,app,system,docker}
}

# 轮转日志文件
rotate_logs() {
    info "开始轮转日志文件..."
    
    local timestamp=$(date +%Y%m%d_%H%M%S)
    
    # 轮转Nginx日志
    if [[ -d "$LOG_DIR/nginx" ]]; then
        info "轮转Nginx日志..."
        for logfile in "$LOG_DIR/nginx"/*.log; do
            if [[ -f "$logfile" && -s "$logfile" ]]; then
                local basename=$(basename "$logfile" .log)
                mv "$logfile" "$LOG_DIR/nginx/${basename}_${timestamp}.log"
                touch "$logfile"
                chmod 644 "$logfile"
                info "已轮转: $basename.log"
            fi
        done
        
        # 发送信号给Nginx重新打开日志文件
        docker exec formalmath-nginx nginx -s reopen 2>/dev/null || true
    fi
    
    # 轮转应用日志
    if [[ -d "$LOG_DIR/app" ]]; then
        info "轮转应用日志..."
        for logfile in "$LOG_DIR/app"/*.log; do
            if [[ -f "$logfile" && -s "$logfile" ]]; then
                local basename=$(basename "$logfile" .log)
                mv "$logfile" "$LOG_DIR/app/${basename}_${timestamp}.log"
                touch "$logfile"
                chmod 644 "$logfile"
                info "已轮转: $basename.log"
            fi
        done
    fi
    
    # 轮转系统日志
    if [[ -d "$LOG_DIR/system" ]]; then
        info "轮转系统日志..."
        for logfile in "$LOG_DIR/system"/*.log; do
            if [[ -f "$logfile" && -s "$logfile" ]]; then
                local basename=$(basename "$logfile" .log)
                mv "$logfile" "$LOG_DIR/system/${basename}_${timestamp}.log"
                touch "$logfile"
                chmod 644 "$logfile"
            fi
        done
    fi
    
    success "日志轮转完成"
}

# 清理过期日志
clean_old_logs() {
    info "清理${RETENTION_DAYS}天前的日志..."
    
    local deleted_count=0
    local freed_space=0
    
    # 清理归档目录中的旧日志
    if [[ -d "$ARCHIVE_DIR" ]]; then
        while IFS= read -r file; do
            local file_size=$(stat -f%z "$file" 2>/dev/null || stat -c%s "$file" 2>/dev/null || echo 0)
            rm -f "$file"
            ((deleted_count++))
            ((freed_space += file_size))
        done < <(find "$ARCHIVE_DIR" -name "*.log*" -mtime +$RETENTION_DAYS 2>/dev/null)
    fi
    
    # 清理各日志目录中的旧轮转文件
    for log_subdir in nginx app system docker; do
        if [[ -d "$LOG_DIR/$log_subdir" ]]; then
            while IFS= read -r file; do
                local file_size=$(stat -f%z "$file" 2>/dev/null || stat -c%s "$file" 2>/dev/null || echo 0)
                rm -f "$file"
                ((deleted_count++))
                ((freed_space += file_size))
            done < <(find "$LOG_DIR/$log_subdir" -name "*_*.log" -mtime +$RETENTION_DAYS 2>/dev/null)
        fi
    done
    
    # 转换为人类可读格式
    local freed_mb=$((freed_space / 1024 / 1024))
    
    success "清理完成: 删除 $deleted_count 个文件，释放 ${freed_mb}MB 空间"
}

# 归档旧日志
archive_logs() {
    info "归档旧日志..."
    
    local timestamp=$(date +%Y%m%d)
    local archive_name="logs_archive_${timestamp}.tar.gz"
    
    mkdir -p "$ARCHIVE_DIR"
    
    # 收集7天前的日志文件
    local files_to_archive=()
    for log_subdir in nginx app system; do
        if [[ -d "$LOG_DIR/$log_subdir" ]]; then
            while IFS= read -r file; do
                files_to_archive+=("$file")
            done < <(find "$LOG_DIR/$log_subdir" -name "*_*.log" -mtime +7 2>/dev/null)
        fi
    done
    
    if [[ ${#files_to_archive[@]} -eq 0 ]]; then
        info "没有需要归档的日志文件"
        return 0
    fi
    
    # 创建归档
    tar -czf "$ARCHIVE_DIR/$archive_name" -C "$PROJECT_ROOT" "${files_to_archive[@]#$PROJECT_ROOT/}" 2>/dev/null || {
        # 如果tar失败，逐个压缩
        for file in "${files_to_archive[@]}"; do
            gzip -f "$file" 2>/dev/null || true
        done
    }
    
    success "归档完成: $archive_name"
}

# 压缩旧日志
compress_logs() {
    info "压缩旧日志文件..."
    
    local compressed_count=0
    
    for log_subdir in nginx app system; do
        if [[ -d "$LOG_DIR/$log_subdir" ]]; then
            while IFS= read -r file; do
                if [[ ! "$file" =~ \.gz$ ]]; then
                    gzip -f "$file"
                    ((compressed_count++))
                fi
            done < <(find "$LOG_DIR/$log_subdir" -name "*_*.log" -mtime +1 2>/dev/null)
        fi
    done
    
    success "压缩完成: $compressed_count 个文件"
}

# 查看日志大小
show_log_size() {
    info "日志大小统计:"
    echo "========================================"
    
    local total_size=0
    
    for log_subdir in nginx app system docker; do
        if [[ -d "$LOG_DIR/$log_subdir" ]]; then
            local dir_size=$(du -sb "$LOG_DIR/$log_subdir" 2>/dev/null | cut -f1 || echo 0)
            local dir_size_mb=$((dir_size / 1024 / 1024))
            total_size=$((total_size + dir_size))
            printf "%-15s %10s MB\n" "$log_subdir:" "$dir_size_mb"
            
            # 显示最大的5个文件
            find "$LOG_DIR/$log_subdir" -type f -printf "%s %p\n" 2>/dev/null | \
                sort -rn | head -5 | while read size filename; do
                local size_mb=$((size / 1024 / 1024))
                printf "  %-50s %6s MB\n" "$(basename "$filename")" "$size_mb"
            done
        fi
    done
    
    local total_mb=$((total_size / 1024 / 1024))
    echo "========================================"
    printf "%-15s %10s MB\n" "总计:" "$total_mb"
    
    # Docker容器日志大小
    echo ""
    info "Docker容器日志大小:"
    docker ps --format "{{.Names}}" | while read container; do
        local log_size=$(docker inspect --format='{{.LogPath}}' "$container" 2>/dev/null | xargs ls -l 2>/dev/null | awk '{print $5}' || echo 0)
        local log_size_mb=$((log_size / 1024 / 1024))
        printf "%-30s %6s MB\n" "$container:" "$log_size_mb"
    done
}

# 配置Docker日志限制
configure_docker_logs() {
    info "配置Docker日志限制..."
    
    # 创建daemon.json配置
    local docker_config='{
  "log-driver": "json-file",
  "log-opts": {
    "max-size": "'"$DOCKER_LOG_MAX_SIZE"'",
    "max-file": "'"$DOCKER_LOG_MAX_FILE"'",
    "labels": "service_name,environment",
    "env": "OS_VERSION"
  }
}'
    
    echo "$docker_config" | sudo tee /etc/docker/daemon.json > /dev/null
    
    warn "Docker配置已更新，需要重启Docker服务生效:"
    echo "  sudo systemctl restart docker"
    
    success "Docker日志配置完成"
}

# 生成日志报告
generate_report() {
    local report_file="$LOG_DIR/report_$(date +%Y%m%d).txt"
    
    info "生成日志报告: $report_file"
    
    {
        echo "FormalMath 日志报告"
        echo "生成时间: $(date '+%Y-%m-%d %H:%M:%S')"
        echo "========================================"
        echo ""
        
        echo "1. 日志目录大小"
        echo "----------------------------------------"
        show_log_size
        
        echo ""
        echo "2. 错误统计（最近24小时）"
        echo "----------------------------------------"
        for logfile in "$LOG_DIR"/*/*.log; do
            if [[ -f "$logfile" ]]; then
                local error_count=$(grep -c "ERROR\|error\|Error" "$logfile" 2>/dev/null || echo 0)
                if [[ $error_count -gt 0 ]]; then
                    printf "%-50s %6s 错误\n" "$(basename "$logfile")" "$error_count"
                fi
            fi
        done
        
        echo ""
        echo "3. Docker容器状态"
        echo "----------------------------------------"
        docker ps --format "table {{.Names}}\t{{.Status}}\t{{.Ports}}"
        
        echo ""
        echo "4. 磁盘使用情况"
        echo "----------------------------------------"
        df -h "$LOG_DIR"
        
    } > "$report_file"
    
    success "报告生成完成: $report_file"
    cat "$report_file"
}

# 设置定时任务
setup_cron() {
    info "设置日志管理定时任务..."
    
    # 每天凌晨4点轮转日志
    local rotate_cron="0 4 * * * $SCRIPT_DIR/log-rotate.sh rotate"
    
    # 每周日凌晨5点清理旧日志
    local clean_cron="0 5 * * 0 $SCRIPT_DIR/log-rotate.sh clean"
    
    # 每天凌晨3点归档日志
    local archive_cron="0 3 * * * $SCRIPT_DIR/log-rotate.sh archive"
    
    # 添加到crontab
    (crontab -l 2>/dev/null | grep -v "$SCRIPT_DIR/log-rotate.sh"; \
     echo "$rotate_cron"; \
     echo "$clean_cron"; \
     echo "$archive_cron") | crontab -
    
    success "定时任务已设置"
    crontab -l | grep "log-rotate"
}

# 主函数
main() {
    local command=""
    
    # 解析参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            -d|--days)
                RETENTION_DAYS="$2"
                shift 2
                ;;
            -s|--size)
                DOCKER_LOG_MAX_SIZE="$2"
                shift 2
                ;;
            -f|--force)
                shift
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            rotate|clean|archive|size|docker|compress|report)
                command=$1
                shift
                ;;
            *)
                error "未知选项: $1"
                show_help
                exit 1
                ;;
        esac
    done
    
    # 初始化
    init_directories
    
    # 执行命令
    case $command in
        rotate)
            rotate_logs
            ;;
        clean)
            clean_old_logs
            ;;
        archive)
            archive_logs
            ;;
        size)
            show_log_size
            ;;
        docker)
            configure_docker_logs
            ;;
        compress)
            compress_logs
            ;;
        report)
            generate_report
            ;;
        *)
            show_help
            exit 1
            ;;
    esac
}

main "$@"
