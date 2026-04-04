#!/bin/bash
# =============================================================================
# FormalMath API - PostgreSQL 备份脚本
# 版本: 1.0.0
# 最后更新: 2026-04-04
#
# 功能:
#   - 全量备份 (pg_dump)
#   - 增量备份 (WAL归档)
#   - 自动清理过期备份
#   - 上传到远程存储 (可选)
#
# 使用方法:
#   ./postgresql_backup.sh [full|incremental|cleanup]
# =============================================================================

set -euo pipefail

# 配置变量
readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly BACKUP_BASE_DIR="/var/backups/formalmath/postgresql"
readonly LOG_DIR="/var/log/formalmath/backup"
readonly TIMESTAMP=$(date +%Y%m%d_%H%M%S)
readonly DATE=$(date +%Y%m%d)

# 数据库配置
DB_HOST="${DB_HOST:-localhost}"
DB_PORT="${DB_PORT:-5432}"
DB_NAME="${DB_NAME:-formalmath}"
DB_USER="${DB_USER:-postgres}"
DB_PASSWORD="${DB_PASSWORD:-}"

# 备份保留策略
FULL_BACKUP_RETENTION_DAYS="${FULL_BACKUP_RETENTION_DAYS:-30}"
INCREMENTAL_BACKUP_RETENTION_DAYS="${INCREMENTAL_BACKUP_RETENTION_DAYS:-7}"

# 远程存储配置 (可选)
S3_BUCKET="${S3_BUCKET:-}"
S3_PREFIX="${S3_PREFIX:-backups/postgresql}"

# 通知配置
ADMIN_EMAIL="${ADMIN_EMAIL:-admin@formalmath.org}"
SLACK_WEBHOOK="${SLACK_WEBHOOK:-}"

# 创建目录
mkdir -p "${BACKUP_BASE_DIR}"/{full,incremental,wal} "${LOG_DIR}"

# 日志函数
log() {
    local level="$1"
    shift
    local message="$*"
    local log_file="${LOG_DIR}/backup_${DATE}.log"
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] [${level}] ${message}" | tee -a "${log_file}"
}

# 发送通知
send_notification() {
    local status="$1"
    local message="$2"
    
    # 发送邮件
    if command -v mail &> /dev/null && [[ -n "${ADMIN_EMAIL}" ]]; then
        echo "${message}" | mail -s "[PostgreSQL Backup] ${status}" "${ADMIN_EMAIL}"
    fi
    
    # 发送Slack通知
    if [[ -n "${SLACK_WEBHOOK}" ]]; then
        curl -s -X POST -H 'Content-type: application/json' \
            --data "{\"text\":\"${status}: ${message}\"}" \
            "${SLACK_WEBHOOK}" || true
    fi
}

# 设置环境变量
export PGHOST="${DB_HOST}"
export PGPORT="${DB_PORT}"
export PGDATABASE="${DB_NAME}"
export PGUSER="${DB_USER}"
export PGPASSWORD="${DB_PASSWORD}"

# 检查依赖
check_dependencies() {
    local deps=("pg_dump" "pg_dumpall" "pg_basebackup")
    for dep in "${deps[@]}"; do
        if ! command -v "${dep}" &> /dev/null; then
            log "ERROR" "依赖未安装: ${dep}"
            exit 1
        fi
    done
}

# 全量备份
full_backup() {
    log "INFO" "开始全量备份..."
    
    local backup_dir="${BACKUP_BASE_DIR}/full/${DATE}"
    local backup_file="${backup_dir}/formalmath_${TIMESTAMP}.sql.gz"
    
    mkdir -p "${backup_dir}"
    
    # 备份数据库
    log "INFO" "备份数据库: ${DB_NAME}"
    if pg_dump -Fc --verbose --blobs --no-owner --no-privileges \
        "${DB_NAME}" 2>> "${LOG_DIR}/backup_${DATE}.log" | \
        gzip > "${backup_file}"; then
        
        # 计算文件大小
        local size=$(du -h "${backup_file}" | cut -f1)
        log "INFO" "全量备份完成: ${backup_file} (大小: ${size})"
        
        # 生成校验和
        sha256sum "${backup_file}" > "${backup_file}.sha256"
        
        # 备份角色和权限
        pg_dumpall --globals-only | gzip > "${backup_dir}/globals_${TIMESTAMP}.sql.gz"
        
        # 上传到S3
        if [[ -n "${S3_BUCKET}" ]]; then
            upload_to_s3 "${backup_file}" "full/"
        fi
        
        send_notification "SUCCESS" "全量备份完成: ${backup_file} (${size})"
    else
        log "ERROR" "全量备份失败"
        send_notification "FAILED" "全量备份失败"
        exit 1
    fi
}

# 物理备份 (pg_basebackup)
physical_backup() {
    log "INFO" "开始物理备份..."
    
    local backup_dir="${BACKUP_BASE_DIR}/physical/${TIMESTAMP}"
    mkdir -p "${backup_dir}"
    
    if pg_basebackup -D "${backup_dir}" -Ft -z -P -v \
        -X fetch 2>> "${LOG_DIR}/backup_${DATE}.log"; then
        log "INFO" "物理备份完成: ${backup_dir}"
        
        # 上传到S3
        if [[ -n "${S3_BUCKET}" ]]; then
            upload_to_s3 "${backup_dir}.tar.gz" "physical/"
        fi
    else
        log "ERROR" "物理备份失败"
        exit 1
    fi
}

# WAL归档备份
wal_backup() {
    log "INFO" "备份WAL文件..."
    
    local wal_dir="${BACKUP_BASE_DIR}/wal"
    mkdir -p "${wal_dir}"
    
    # 触发WAL切换
    psql -c "SELECT pg_switch_wal();" || true
    
    # 复制WAL文件
    if [[ -d "/var/lib/postgresql/archive" ]]; then
        cp -r /var/lib/postgresql/archive/* "${wal_dir}/" 2>/dev/null || true
        log "INFO" "WAL文件备份完成"
    fi
}

# 清理过期备份
cleanup_old_backups() {
    log "INFO" "清理过期备份..."
    
    # 清理全量备份
    local deleted_count=0
    while IFS= read -r -d '' file; do
        rm -rf "${file}"
        ((deleted_count++)) || true
        log "INFO" "删除过期全量备份: ${file}"
    done < <(find "${BACKUP_BASE_DIR}/full" -maxdepth 1 -type d -mtime +${FULL_BACKUP_RETENTION_DAYS} -print0)
    
    # 清理增量备份
    while IFS= read -r -d '' file; do
        rm -rf "${file}"
        ((deleted_count++)) || true
        log "INFO" "删除过期增量备份: ${file}"
    done < <(find "${BACKUP_BASE_DIR}/incremental" -maxdepth 1 -type d -mtime +${INCREMENTAL_BACKUP_RETENTION_DAYS} -print0 2>/dev/null || true)
    
    # 清理旧日志
    find "${LOG_DIR}" -name "*.log" -mtime +30 -delete 2>/dev/null || true
    
    log "INFO" "清理完成，删除 ${deleted_count} 个备份"
}

# 上传到S3
upload_to_s3() {
    local file="$1"
    local prefix="$2"
    
    if command -v aws &> /dev/null; then
        log "INFO" "上传到S3: ${S3_BUCKET}/${S3_PREFIX}/${prefix}"
        aws s3 cp "${file}" "s3://${S3_BUCKET}/${S3_PREFIX}/${prefix}$(basename "${file}")" \
            --storage-class STANDARD_IA || true
    else
        log "WARN" "AWS CLI未安装，跳过S3上传"
    fi
}

# 验证备份
verify_backup() {
    local backup_file="$1"
    
    log "INFO" "验证备份文件: ${backup_file}"
    
    # 验证文件存在
    if [[ ! -f "${backup_file}" ]]; then
        log "ERROR" "备份文件不存在: ${backup_file}"
        return 1
    fi
    
    # 验证校验和
    if [[ -f "${backup_file}.sha256" ]]; then
        if ! sha256sum -c "${backup_file}.sha256" > /dev/null 2>&1; then
            log "ERROR" "备份文件校验失败: ${backup_file}"
            return 1
        fi
    fi
    
    # 验证压缩文件完整性
    if [[ "${backup_file}" == *.gz ]]; then
        if ! gzip -t "${backup_file}" 2>/dev/null; then
            log "ERROR" "备份文件损坏: ${backup_file}"
            return 1
        fi
    fi
    
    log "INFO" "备份验证通过"
    return 0
}

# 显示备份状态
show_status() {
    echo "========================================"
    echo "      PostgreSQL 备份状态"
    echo "========================================"
    echo "备份目录: ${BACKUP_BASE_DIR}"
    echo "日志目录: ${LOG_DIR}"
    echo ""
    echo "全量备份:"
    du -sh "${BACKUP_BASE_DIR}/full"/* 2>/dev/null | tail -5 || echo "  无全量备份"
    echo ""
    echo "磁盘使用情况:"
    df -h "${BACKUP_BASE_DIR}"
    echo ""
    echo "最新日志:"
    tail -10 "${LOG_DIR}/backup_${DATE}.log" 2>/dev/null || echo "  无日志文件"
}

# 使用说明
usage() {
    cat << EOF
使用方法: $0 [命令] [选项]

命令:
  full          执行全量备份
  physical      执行物理备份
  wal           备份WAL文件
  cleanup       清理过期备份
  verify        验证最新备份
  status        显示备份状态
  restore       恢复备份 (交互式)

选项:
  -h, --help    显示帮助信息

环境变量:
  DB_HOST       数据库主机 (默认: localhost)
  DB_PORT       数据库端口 (默认: 5432)
  DB_NAME       数据库名称 (默认: formalmath)
  DB_USER       数据库用户 (默认: postgres)
  DB_PASSWORD   数据库密码
  S3_BUCKET     S3存储桶名称
  ADMIN_EMAIL   管理员邮箱

示例:
  # 执行全量备份
  $0 full

  # 清理过期备份
  $0 cleanup

  # 显示备份状态
  $0 status

EOF
}

# 主函数
main() {
    case "${1:-}" in
        full)
            check_dependencies
            full_backup
            ;;
        physical)
            check_dependencies
            physical_backup
            ;;
        wal)
            wal_backup
            ;;
        cleanup)
            cleanup_old_backups
            ;;
        verify)
            latest_backup=$(find "${BACKUP_BASE_DIR}/full" -name "*.sql.gz" -type f -printf '%T@ %p\n' | sort -n | tail -1 | cut -d' ' -f2-)
            if [[ -n "${latest_backup}" ]]; then
                verify_backup "${latest_backup}"
            else
                log "ERROR" "未找到备份文件"
                exit 1
            fi
            ;;
        status)
            show_status
            ;;
        -h|--help|help)
            usage
            exit 0
            ;;
        *)
            usage
            exit 1
            ;;
    esac
}

main "$@"
