#!/bin/bash
# ============================================
# FormalMath - 备份任务调度脚本
# 支持全量备份、增量备份、云存储同步
# ============================================

set -euo pipefail

# 配置
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
BACKUP_DIR="${PROJECT_ROOT}/backups"
DATA_DIR="${PROJECT_ROOT}/data"
LOG_FILE="${PROJECT_ROOT}/logs/backup.log"
CONFIG_FILE="${PROJECT_ROOT}/config/backup.conf"

# 默认配置
RETENTION_DAYS=30
FULL_BACKUP_DAY=0  # 周日
S3_BUCKET=""
S3_REGION=""
ENCRYPTION_KEY=""
NOTIFICATION_EMAIL=""

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
    echo "[$timestamp] [$level] $message" | tee -a "$LOG_FILE"
}

info() { log "INFO" "$@"; }
warn() { log "WARN" "$@"; }
error() { log "ERROR" "$@"; }
success() { log "SUCCESS" "$@"; }

# 显示帮助
show_help() {
    cat << EOF
FormalMath 备份调度脚本

用法: $0 [选项] [命令]

命令:
    full        执行全量备份
    incremental 执行增量备份
    database    备份数据库
    files       备份文件
    sync        同步到云存储
    restore     恢复备份
    list        列出备份
    verify      验证备份完整性
    schedule    设置定时任务
    status      查看备份状态

选项:
    -d, --destination   备份目标路径
    -k, --key          加密密钥
    -r, --retention    保留天数
    -h, --help         显示帮助

示例:
    $0 full
    $0 incremental
    $0 sync
    $0 restore -d 20240101_120000
EOF
}

# 加载配置
load_config() {
    if [[ -f "$CONFIG_FILE" ]]; then
        info "加载配置文件: $CONFIG_FILE"
        source "$CONFIG_FILE"
    fi
    
    # 加载环境变量
    if [[ -f "$PROJECT_ROOT/.env.production" ]]; then
        export $(grep -v '^#' "$PROJECT_ROOT/.env.production" | xargs)
    fi
}

# 初始化
init() {
    info "初始化备份系统..."
    mkdir -p "$BACKUP_DIR"/{full,incremental,database,files} "$(dirname "$LOG_FILE")"
    
    # 检查依赖
    check_dependencies
}

# 检查依赖
check_dependencies() {
    local deps=("tar" "gzip" "rsync")
    
    for dep in "${deps[@]}"; do
        if ! command -v "$dep" &> /dev/null; then
            warn "依赖未安装: $dep"
        fi
    done
    
    # 检查AWS CLI（用于S3同步）
    if [[ -n "$S3_BUCKET" ]] && ! command -v aws &> /dev/null; then
        warn "AWS CLI未安装，云存储同步将不可用"
    fi
}

# 全量备份
full_backup() {
    info "开始全量备份..."
    
    local timestamp=$(date +%Y%m%d_%H%M%S)
    local backup_name="full_backup_${timestamp}"
    local backup_path="${BACKUP_DIR}/full/${backup_name}.tar.gz"
    
    mkdir -p "${BACKUP_DIR}/full"
    
    # 备份数据目录
    info "备份数据目录..."
    tar -czf "$backup_path" -C "$PROJECT_ROOT" \
        --exclude='*.log' \
        --exclude='node_modules' \
        --exclude='__pycache__' \
        --exclude='.git' \
        data/ 2>/dev/null || true
    
    # 备份配置文件
    info "备份配置文件..."
    tar -czf "${BACKUP_DIR}/full/config_${timestamp}.tar.gz" -C "$PROJECT_ROOT" \
        .env.production \
        docker-compose.production.yml \
        nginx/ \
        config/ 2>/dev/null || true
    
    # 生成校验和
    sha256sum "$backup_path" > "${backup_path}.sha256"
    
    # 加密备份（如果提供了密钥）
    if [[ -n "$ENCRYPTION_KEY" ]]; then
        info "加密备份..."
        gpg --symmetric --cipher-algo AES256 --passphrase "$ENCRYPTION_KEY" \
            --batch --yes -o "${backup_path}.gpg" "$backup_path"
        rm -f "$backup_path"
        backup_path="${backup_path}.gpg"
    fi
    
    local backup_size=$(du -sh "$backup_path" | cut -f1)
    success "全量备份完成: $backup_path (大小: $backup_size)"
    
    # 发送通知
    send_notification "全量备份完成" "备份文件: $backup_name\n大小: $backup_size"
}

# 增量备份
incremental_backup() {
    info "开始增量备份..."
    
    local timestamp=$(date +%Y%m%d_%H%M%S)
    local backup_name="incremental_${timestamp}"
    local backup_path="${BACKUP_DIR}/incremental/${backup_name}"
    local snapshot_file="${BACKUP_DIR}/.snapshot"
    
    mkdir -p "${BACKUP_DIR}/incremental"
    
    # 使用rsync进行增量备份
    rsync -avz --delete --link-dest="$BACKUP_DIR/full" \
        --exclude='*.log' \
        --exclude='node_modules' \
        --exclude='__pycache__' \
        "$DATA_DIR/" "$backup_path/" 2>/dev/null || true
    
    # 打包增量备份
    tar -czf "${backup_path}.tar.gz" -C "$BACKUP_DIR/incremental" "$backup_name"
    rm -rf "$backup_path"
    
    local backup_size=$(du -sh "${backup_path}.tar.gz" | cut -f1)
    success "增量备份完成: ${backup_path}.tar.gz (大小: $backup_size)"
}

# 备份数据库
backup_database() {
    info "备份数据库..."
    
    local timestamp=$(date +%Y%m%d_%H%M%S)
    local backup_path="${BACKUP_DIR}/database/db_${timestamp}.sql"
    
    mkdir -p "${BACKUP_DIR}/database"
    
    # 检查容器运行状态
    if docker ps | grep -q "formalmath-backend"; then
        # 导出SQLite数据库
        docker exec formalmath-backend sh -c 'sqlite3 /app/data/formalmath.db ".dump"' > "$backup_path" 2>/dev/null || {
            # 如果sqlite3命令失败，直接复制文件
            docker cp "formalmath-backend:/app/data/formalmath.db" "${backup_path}.db"
            backup_path="${backup_path}.db"
        }
        
        # 压缩备份
        gzip -f "$backup_path" 2>/dev/null || true
        
        local backup_size=$(du -sh "${backup_path}.gz" 2>/dev/null || du -sh "$backup_path" | cut -f1)
        success "数据库备份完成 (大小: $backup_size)"
    else
        error "后端容器未运行，无法备份数据库"
        return 1
    fi
}

# 备份文件
backup_files() {
    info "备份文件..."
    
    local timestamp=$(date +%Y%m%d_%H%M%S)
    local backup_path="${BACKUP_DIR}/files/files_${timestamp}.tar.gz"
    
    mkdir -p "${BACKUP_DIR}/files"
    
    # 备份重要文件
    tar -czf "$backup_path" -C "$PROJECT_ROOT" \
        --exclude='*.log' \
        --exclude='node_modules' \
        --exclude='__pycache__' \
        --exclude='backups' \
        api/ \
        nginx/ \
        scripts/ \
        config/ 2>/dev/null || true
    
    local backup_size=$(du -sh "$backup_path" | cut -f1)
    success "文件备份完成 (大小: $backup_size)"
}

# 同步到云存储
sync_to_cloud() {
    info "同步备份到云存储..."
    
    if [[ -z "$S3_BUCKET" ]]; then
        warn "未配置云存储，跳过同步"
        return 0
    fi
    
    # 检查AWS CLI
    if ! command -v aws &> /dev/null; then
        error "AWS CLI未安装"
        return 1
    fi
    
    # 同步到S3
    aws s3 sync "$BACKUP_DIR/" "s3://$S3_BUCKET/backups/" \
        --storage-class STANDARD_IA \
        --exclude "*.tmp" \
        --delete
    
    success "云存储同步完成"
}

# 恢复备份
restore_backup() {
    local backup_date="${1:-}"
    
    if [[ -z "$backup_date" ]]; then
        info "可用的备份:"
        ls -la "$BACKUP_DIR"/*/
        read -p "请输入要恢复的备份日期 (格式: YYYYMMDD_HHMMSS): " backup_date
    fi
    
    local backup_path="${BACKUP_DIR}/full/full_backup_${backup_date}.tar.gz"
    
    if [[ ! -f "$backup_path" ]]; then
        error "备份文件不存在: $backup_path"
        return 1
    fi
    
    warn "即将恢复备份，这将覆盖当前数据！"
    read -p "确定要继续吗? (yes/no) " confirm
    if [[ "$confirm" != "yes" ]]; then
        info "操作已取消"
        return 0
    fi
    
    info "恢复备份: $backup_path"
    
    # 创建临时恢复目录
    local restore_temp="${BACKUP_DIR}/.restore_temp"
    mkdir -p "$restore_temp"
    
    # 解压备份
    tar -xzf "$backup_path" -C "$restore_temp"
    
    # 停止服务
    info "停止服务..."
    docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" stop backend 2>/dev/null || true
    
    # 恢复数据
    cp -r "$restore_temp/data/"* "$DATA_DIR/" 2>/dev/null || true
    
    # 启动服务
    info "启动服务..."
    docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" start backend 2>/dev/null || true
    
    # 清理临时目录
    rm -rf "$restore_temp"
    
    success "备份恢复完成"
}

# 列出备份
list_backups() {
    info "备份列表:"
    echo "========================================"
    
    for backup_type in full incremental database files; do
        if [[ -d "$BACKUP_DIR/$backup_type" ]]; then
            echo ""
            echo "$backup_type 备份:"
            ls -lh "$BACKUP_DIR/$backup_type" 2>/dev/null | tail -n +2 || echo "  无备份文件"
        fi
    done
    
    echo ""
    echo "========================================"
    echo "备份总大小:"
    du -sh "$BACKUP_DIR"
}

# 验证备份完整性
verify_backup() {
    info "验证备份完整性..."
    
    local failed=0
    
    for backup_file in "$BACKUP_DIR"/*/*.tar.gz; do
        if [[ -f "$backup_file" ]]; then
            info "验证: $(basename "$backup_file")"
            
            # 验证gzip完整性
            if gzip -t "$backup_file" 2>/dev/null; then
                success "  ✓ 文件完整性正常"
            else
                error "  ✗ 文件损坏"
                ((failed++))
            fi
            
            # 验证校验和
            local sha_file="${backup_file}.sha256"
            if [[ -f "$sha_file" ]]; then
                if sha256sum -c "$sha_file" &>/dev/null; then
                    success "  ✓ 校验和验证通过"
                else
                    error "  ✗ 校验和不匹配"
                    ((failed++))
                fi
            fi
        fi
    done
    
    if [[ $failed -eq 0 ]]; then
        success "所有备份验证通过"
    else
        error "$failed 个备份验证失败"
        return 1
    fi
}

# 查看备份状态
backup_status() {
    info "备份状态报告:"
    echo "========================================"
    
    # 统计备份数量和大小
    for backup_type in full incremental database files; do
        if [[ -d "$BACKUP_DIR/$backup_type" ]]; then
            local count=$(find "$BACKUP_DIR/$backup_type" -type f | wc -l)
            local size=$(du -sh "$BACKUP_DIR/$backup_type" 2>/dev/null | cut -f1)
            printf "%-15s %6s 个文件   %10s\n" "$backup_type:" "$count" "$size"
        fi
    done
    
    echo "----------------------------------------"
    printf "%-15s %10s\n" "总计:" "$(du -sh "$BACKUP_DIR" | cut -f1)"
    
    # 检查最近备份时间
    echo ""
    info "最近备份:"
    find "$BACKUP_DIR" -type f -printf "%T@ %p\n" 2>/dev/null | \
        sort -rn | head -5 | while read timestamp file; do
        local date=$(date -d "@$timestamp" '+%Y-%m-%d %H:%M:%S' 2>/dev/null || date -r "$timestamp" '+%Y-%m-%d %H:%M:%S')
        printf "  %s  %s\n" "$date" "$(basename "$file")"
    done
    
    # 检查云存储同步状态
    if [[ -n "$S3_BUCKET" ]]; then
        echo ""
        info "云存储状态:"
        if command -v aws &> /dev/null; then
            aws s3 ls "s3://$S3_BUCKET/backups/" --recursive --summarize 2>/dev/null | tail -2 || echo "  无法获取云存储状态"
        else
            echo "  AWS CLI未安装"
        fi
    fi
}

# 清理旧备份
cleanup_old_backups() {
    info "清理${RETENTION_DAYS}天前的备份..."
    
    local deleted_count=0
    local freed_space=0
    
    for backup_type in full incremental database files; do
        if [[ -d "$BACKUP_DIR/$backup_type" ]]; then
            while IFS= read -r file; do
                local file_size=$(stat -f%z "$file" 2>/dev/null || stat -c%s "$file" 2>/dev/null || echo 0)
                rm -f "$file"
                rm -f "${file}.sha256" 2>/dev/null || true
                ((deleted_count++))
                ((freed_space += file_size))
            done < <(find "$BACKUP_DIR/$backup_type" -type f -mtime +$RETENTION_DAYS 2>/dev/null)
        fi
    done
    
    local freed_mb=$((freed_space / 1024 / 1024))
    success "清理完成: 删除 $deleted_count 个文件，释放 ${freed_mb}MB 空间"
}

# 发送通知
send_notification() {
    local subject="$1"
    local message="$2"
    
    if [[ -n "$NOTIFICATION_EMAIL" ]]; then
        echo -e "$message" | mail -s "[FormalMath Backup] $subject" "$NOTIFICATION_EMAIL" 2>/dev/null || true
    fi
    
    # 也可以发送到Slack、企业微信等
    # webhook通知逻辑可以在这里添加
}

# 设置定时任务
schedule_backups() {
    info "设置备份定时任务..."
    
    # 每天凌晨2点执行增量备份
    local incremental_cron="0 2 * * * $SCRIPT_DIR/backup-scheduler.sh incremental >> $LOG_FILE 2>&1"
    
    # 每周日凌晨3点执行全量备份
    local full_cron="0 3 * * 0 $SCRIPT_DIR/backup-scheduler.sh full >> $LOG_FILE 2>&1"
    
    # 每天凌晨1点备份数据库
    local db_cron="0 1 * * * $SCRIPT_DIR/backup-scheduler.sh database >> $LOG_FILE 2>&1"
    
    # 每天凌晨4点同步到云存储
    local sync_cron="0 4 * * * $SCRIPT_DIR/backup-scheduler.sh sync >> $LOG_FILE 2>&1"
    
    # 每周一凌晨5点清理旧备份
    local cleanup_cron="0 5 * * 1 $SCRIPT_DIR/backup-scheduler.sh cleanup >> $LOG_FILE 2>&1"
    
    # 添加到crontab
    (crontab -l 2>/dev/null | grep -v "$SCRIPT_DIR/backup-scheduler.sh"; \
     echo "$incremental_cron"; \
     echo "$full_cron"; \
     echo "$db_cron"; \
     echo "$sync_cron"; \
     echo "$cleanup_cron") | crontab -
    
    success "定时任务已设置"
    crontab -l | grep "backup-scheduler"
}

# 主函数
main() {
    local command=""
    local restore_date=""
    
    # 解析参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            -d|--destination)
                restore_date="$2"
                shift 2
                ;;
            -k|--key)
                ENCRYPTION_KEY="$2"
                shift 2
                ;;
            -r|--retention)
                RETENTION_DAYS="$2"
                shift 2
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            full|incremental|database|files|sync|restore|list|verify|schedule|status|cleanup)
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
    
    # 加载配置
    load_config
    
    # 初始化
    init
    
    # 执行命令
    case $command in
        full)
            full_backup
            ;;
        incremental)
            incremental_backup
            ;;
        database)
            backup_database
            ;;
        files)
            backup_files
            ;;
        sync)
            sync_to_cloud
            ;;
        restore)
            restore_backup "$restore_date"
            ;;
        list)
            list_backups
            ;;
        verify)
            verify_backup
            ;;
        schedule)
            schedule_backups
            ;;
        status)
            backup_status
            ;;
        cleanup)
            cleanup_old_backups
            ;;
        *)
            show_help
            exit 1
            ;;
    esac
}

main "$@"
