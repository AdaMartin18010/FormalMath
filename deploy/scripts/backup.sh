#!/bin/bash
# ============================================
# FormalMath - 自动备份脚本
# 支持数据库、Redis、配置的备份
# ============================================

set -euo pipefail

# 配置
BACKUP_DIR="${BACKUP_DIR:-/backups/formalmath}"
DATE=$(date +%Y%m%d_%H%M%S)
RETENTION_DAYS=${RETENTION_DAYS:-30}
S3_BUCKET="${S3_BUCKET:-}"
NOTIFICATION_EMAIL="${NOTIFICATION_EMAIL:-ops@formalmath.org}"

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# 日志函数
log_info() { echo -e "${BLUE}[INFO]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"; }
log_success() { echo -e "${GREEN}[SUCCESS]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"; }

# 创建备份目录
mkdir -p "$BACKUP_DIR"

# 备份PostgreSQL
backup_postgres() {
    log_info "开始PostgreSQL备份..."
    
    local backup_file="$BACKUP_DIR/postgres_${DATE}.sql.gz"
    
    if docker exec formalmath-db pg_dump -U formalmath formalmath_db 2>/dev/null | gzip > "$backup_file"; then
        log_success "PostgreSQL备份完成: $backup_file"
        ls -lh "$backup_file"
    else
        log_error "PostgreSQL备份失败"
        return 1
    fi
}

# 备份Redis
backup_redis() {
    log_info "开始Redis备份..."
    
    local backup_file="$BACKUP_DIR/redis_${DATE}.rdb"
    
    # 触发RDB保存
    if docker exec formalmath-redis redis-cli SAVE > /dev/null 2>&1; then
        # 复制RDB文件
        if docker cp formalmath-redis:/data/dump.rdb "$backup_file"; then
            log_success "Redis备份完成: $backup_file"
            ls -lh "$backup_file"
        else
            log_error "Redis备份失败"
            return 1
        fi
    else
        log_error "Redis SAVE命令失败"
        return 1
    fi
}

# 备份配置文件
backup_configs() {
    log_info "开始配置文件备份..."
    
    local backup_file="$BACKUP_DIR/configs_${DATE}.tar.gz"
    
    tar -czf "$backup_file" \
        -C "$(dirname "$BACKUP_DIR")" \
        docker-compose.production.yml \
        nginx.conf \
        .env.production \
        2>/dev/null || true
    
    if [ -f "$backup_file" ]; then
        log_success "配置文件备份完成: $backup_file"
        ls -lh "$backup_file"
    else
        log_warn "配置文件备份可能不完整"
    fi
}

# 上传到S3
upload_to_s3() {
    if [ -z "$S3_BUCKET" ]; then
        log_info "未配置S3_BUCKET，跳过上传到S3"
        return 0
    fi
    
    log_info "开始上传到S3..."
    
    for file in "$BACKUP_DIR"/*_${DATE}.*; do
        if [ -f "$file" ]; then
            local filename
            filename=$(basename "$file")
            
            if aws s3 cp "$file" "s3://$S3_BUCKET/backups/$filename"; then
                log_success "已上传: $filename"
            else
                log_error "上传失败: $filename"
            fi
        fi
    done
}

# 清理旧备份
cleanup_old_backups() {
    log_info "清理超过${RETENTION_DAYS}天的旧备份..."
    
    local deleted=0
    
    while IFS= read -r file; do
        log_info "删除旧备份: $file"
        rm -f "$file"
        deleted=$((deleted + 1))
    done < <(find "$BACKUP_DIR" -type f -mtime +$RETENTION_DAYS)
    
    log_success "已清理 $deleted 个旧备份文件"
}

# 发送通知
send_notification() {
    local status=$1
    local message=$2
    
    if command -v mail &> /dev/null; then
        echo "$message" | mail -s "FormalMath备份 $status" "$NOTIFICATION_EMAIL"
    fi
    
    # 也可以发送到Slack
    if [ -n "${SLACK_WEBHOOK_URL:-}" ]; then
        curl -s -X POST -H 'Content-type: application/json' \
            --data "{\"text\":\"FormalMath备份 $status: $message\"}" \
            "$SLACK_WEBHOOK_URL" > /dev/null || true
    fi
}

# 主函数
main() {
    echo "=============================================="
    echo "FormalMath 自动备份"
    echo "时间: $(date)"
    echo "备份目录: $BACKUP_DIR"
    echo "=============================================="
    echo ""
    
    local exit_code=0
    
    # 执行备份
    backup_postgres || exit_code=1
    echo ""
    
    backup_redis || exit_code=1
    echo ""
    
    backup_configs
    echo ""
    
    # 上传到S3
    upload_to_s3
    echo ""
    
    # 清理旧备份
    cleanup_old_backups
    echo ""
    
    # 总结
    echo "=============================================="
    if [ $exit_code -eq 0 ]; then
        log_success "备份完成！"
        send_notification "成功" "所有备份任务已完成"
    else
        log_error "备份过程中出现错误"
        send_notification "失败" "部分备份任务失败，请检查日志"
    fi
    echo "=============================================="
    
    return $exit_code
}

# 运行主函数
main "$@"
