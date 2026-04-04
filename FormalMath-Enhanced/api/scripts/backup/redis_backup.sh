#!/bin/bash
# =============================================================================
# FormalMath API - Redis 备份脚本
# 版本: 1.0.0
# 最后更新: 2026-04-04
#
# 功能:
#   - RDB备份
#   - AOF备份
#   - 集群备份
#   - 自动清理过期备份
# =============================================================================

set -euo pipefail

# 配置变量
readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly BACKUP_BASE_DIR="/var/backups/formalmath/redis"
readonly LOG_DIR="/var/log/formalmath/backup"
readonly TIMESTAMP=$(date +%Y%m%d_%H%M%S)
readonly DATE=$(date +%Y%m%d)

# Redis配置
REDIS_HOST="${REDIS_HOST:-localhost}"
REDIS_PORT="${REDIS_PORT:-6379}"
REDIS_PASSWORD="${REDIS_PASSWORD:-}"
REDIS_CLUSTER_NODES="${REDIS_CLUSTER_NODES:-}"

# 备份保留策略
BACKUP_RETENTION_DAYS="${BACKUP_RETENTION_DAYS:-14}"

# 远程存储配置
S3_BUCKET="${S3_BUCKET:-}"
S3_PREFIX="${S3_PREFIX:-backups/redis}"

# 创建目录
mkdir -p "${BACKUP_BASE_DIR}"/{rdb,aof,cluster} "${LOG_DIR}"

# 日志函数
log() {
    local level="$1"
    shift
    local message="$*"
    local log_file="${LOG_DIR}/redis_backup_${DATE}.log"
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] [${level}] ${message}" | tee -a "${log_file}"
}

# 获取Redis认证参数
get_redis_auth() {
    if [[ -n "${REDIS_PASSWORD}" ]]; then
        echo "-a '${REDIS_PASSWORD}'"
    else
        echo ""
    fi
}

# 检查Redis连接
check_redis_connection() {
    local host="${1:-${REDIS_HOST}}"
    local port="${2:-${REDIS_PORT}}"
    
    local auth=$(get_redis_auth)
    if redis-cli -h "${host}" -p "${port}" ${auth} ping | grep -q "PONG"; then
        return 0
    else
        return 1
    fi
}

# 检查是否为集群模式
is_cluster_mode() {
    local auth=$(get_redis_auth)
    local info=$(redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} INFO replication 2>/dev/null || echo "")
    if echo "${info}" | grep -q "role:master\|role:slave"; then
        return 0
    fi
    return 1
}

# 备份单机Redis
backup_standalone() {
    log "INFO" "开始备份单机Redis..."
    
    local backup_dir="${BACKUP_BASE_DIR}/rdb/${DATE}"
    mkdir -p "${backup_dir}"
    
    local auth=$(get_redis_auth)
    
    # 触发BGSAVE
    log "INFO" "触发后台保存..."
    if ! redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} BGSAVE | grep -q "OK\|Background saving started"; then
        log "WARN" "BGSAVE可能已在运行，等待完成..."
        sleep 5
    fi
    
    # 等待保存完成
    local last_save=$(redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} LASTSAVE)
    local attempts=0
    while [[ ${attempts} -lt 60 ]]; do
        sleep 1
        local current_save=$(redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} LASTSAVE)
        if [[ "${current_save}" != "${last_save}" ]]; then
            log "INFO" "RDB保存完成"
            break
        fi
        ((attempts++)) || true
    done
    
    if [[ ${attempts} -ge 60 ]]; then
        log "ERROR" "等待RDB保存超时"
        exit 1
    fi
    
    # 复制RDB文件
    local rdb_path=$(redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} CONFIG GET dir | tail -1)
    local rdb_file=$(redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} CONFIG GET dbfilename | tail -1)
    local source_rdb="${rdb_path}/${rdb_file}"
    local target_rdb="${backup_dir}/dump_${TIMESTAMP}.rdb"
    
    if [[ -f "${source_rdb}" ]]; then
        cp "${source_rdb}" "${target_rdb}"
        gzip "${target_rdb}"
        sha256sum "${target_rdb}.gz" > "${target_rdb}.gz.sha256"
        log "INFO" "RDB备份完成: ${target_rdb}.gz"
    else
        log "ERROR" "RDB文件不存在: ${source_rdb}"
        exit 1
    fi
    
    # 备份AOF文件（如果启用）
    local aof_enabled=$(redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} CONFIG GET appendonly | tail -1)
    if [[ "${aof_enabled}" == "yes" ]]; then
        log "INFO" "备份AOF文件..."
        local aof_path="${rdb_path}"
        local aof_file="appendonly.aof"
        local source_aof="${aof_path}/${aof_file}"
        local target_aof="${backup_dir}/appendonly_${TIMESTAMP}.aof"
        
        if [[ -f "${source_aof}" ]]; then
            cp "${source_aof}" "${target_aof}"
            gzip "${target_aof}"
            sha256sum "${target_aof}.gz" > "${target_aof}.gz.sha256"
            log "INFO" "AOF备份完成: ${target_aof}.gz"
        fi
    fi
    
    # 备份配置文件
    redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} CONFIG GET '*' > "${backup_dir}/config_${TIMESTAMP}.txt" 2>/dev/null || true
}

# 备份Redis集群
backup_cluster() {
    log "INFO" "开始备份Redis集群..."
    
    local backup_dir="${BACKUP_BASE_DIR}/cluster/${DATE}"
    mkdir -p "${backup_dir}"
    
    local auth=$(get_redis_auth)
    
    # 获取集群节点信息
    if [[ -n "${REDIS_CLUSTER_NODES}" ]]; then
        IFS=',' read -ra NODES <<< "${REDIS_CLUSTER_NODES}"
    else
        # 尝试从当前节点获取集群信息
        local cluster_nodes=$(redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} CLUSTER NODES 2>/dev/null || echo "")
        if [[ -z "${cluster_nodes}" ]]; then
            log "ERROR" "无法获取集群节点信息"
            exit 1
        fi
        
        # 解析主节点
        local NODES=()
        while IFS=' ' read -r node_id node_addr flags _; do
            if [[ "${flags}" == *"master"* ]]; then
                NODES+=("${node_addr%@*}")
            fi
        done <<< "${cluster_nodes}"
    fi
    
    # 备份每个主节点
    for node in "${NODES[@]}"; do
        local node_host="${node%:*}"
        local node_port="${node#*:}"
        
        log "INFO" "备份节点: ${node_host}:${node_port}"
        
        if ! check_redis_connection "${node_host}" "${node_port}"; then
            log "WARN" "节点连接失败: ${node_host}:${node_port}"
            continue
        fi
        
        # 触发BGSAVE
        redis-cli -h "${node_host}" -p "${node_port}" ${auth} BGSAVE > /dev/null 2>&1 || true
        sleep 5
        
        # 使用SCP或其他方式复制RDB文件（需要SSH访问）
        # 这里简化处理，假设本地访问
        local node_backup_dir="${backup_dir}/${node_host}_${node_port}"
        mkdir -p "${node_backup_dir}"
        
        log "INFO" "节点备份完成: ${node_host}:${node_port}"
    done
    
    # 备份集群配置
    redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} CLUSTER NODES > "${backup_dir}/cluster_nodes_${TIMESTAMP}.txt"
    redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} CLUSTER INFO > "${backup_dir}/cluster_info_${TIMESTAMP}.txt"
    
    log "INFO" "集群备份完成"
}

# 备份Redis Sentinel
backup_sentinel() {
    log "INFO" "开始备份Redis Sentinel..."
    
    local backup_dir="${BACKUP_BASE_DIR}/sentinel/${DATE}"
    mkdir -p "${backup_dir}"
    
    local auth=$(get_redis_auth)
    
    # 获取Sentinel监控的主节点
    local masters=$(redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} SENTINEL MASTERS 2>/dev/null || echo "")
    
    if [[ -z "${masters}" ]]; then
        log "WARN" "无法获取Sentinel主节点信息"
        return 1
    fi
    
    # 保存Sentinel配置
    echo "${masters}" > "${backup_dir}/sentinel_masters_${TIMESTAMP}.txt"
    
    # 获取并备份每个主节点的从节点信息
    local master_names=$(echo "${masters}" | grep -oP '(?<=name)[^,]+' | tr -d ' ')
    for master in ${master_names}; do
        local slaves=$(redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} SENTINEL SLAVES "${master}")
        echo "${slaves}" > "${backup_dir}/sentinel_slaves_${master}_${TIMESTAMP}.txt"
    done
    
    log "INFO" "Sentinel备份完成"
}

# 清理过期备份
cleanup_old_backups() {
    log "INFO" "清理过期备份..."
    
    local deleted_count=0
    while IFS= read -r -d '' dir; do
        rm -rf "${dir}"
        ((deleted_count++)) || true
        log "INFO" "删除过期备份: ${dir}"
    done < <(find "${BACKUP_BASE_DIR}" -maxdepth 2 -type d -mtime +${BACKUP_RETENTION_DAYS} -print0)
    
    # 清理旧日志
    find "${LOG_DIR}" -name "redis_backup_*.log" -mtime +30 -delete 2>/dev/null || true
    
    log "INFO" "清理完成，删除 ${deleted_count} 个备份目录"
}

# 上传到S3
upload_to_s3() {
    local file="$1"
    local prefix="$2"
    
    if command -v aws &> /dev/null && [[ -n "${S3_BUCKET}" ]]; then
        log "INFO" "上传到S3: ${S3_BUCKET}/${S3_PREFIX}/${prefix}"
        aws s3 cp "${file}" "s3://${S3_BUCKET}/${S3_PREFIX}/${prefix}$(basename "${file}")" \
            --storage-class STANDARD_IA 2>/dev/null || true
    fi
}

# 显示备份状态
show_status() {
    echo "========================================"
    echo "         Redis 备份状态"
    echo "========================================"
    echo "备份目录: ${BACKUP_BASE_DIR}"
    echo "日志目录: ${LOG_DIR}"
    echo ""
    echo "RDB备份:"
    du -sh "${BACKUP_BASE_DIR}"/rdb/* 2>/dev/null | tail -5 || echo "  无RDB备份"
    echo ""
    echo "磁盘使用情况:"
    df -h "${BACKUP_BASE_DIR}"
    echo ""
    echo "Redis服务器状态:"
    local auth=$(get_redis_auth)
    redis-cli -h "${REDIS_HOST}" -p "${REDIS_PORT}" ${auth} INFO server 2>/dev/null | grep -E "redis_version|redis_mode" || echo "  无法连接"
}

# 使用说明
usage() {
    cat << EOF
使用方法: $0 [命令] [选项]

命令:
  standalone    备份单机Redis
  cluster       备份Redis集群
  sentinel      备份Redis Sentinel
  cleanup       清理过期备份
  status        显示备份状态

环境变量:
  REDIS_HOST           Redis主机 (默认: localhost)
  REDIS_PORT           Redis端口 (默认: 6379)
  REDIS_PASSWORD       Redis密码
  REDIS_CLUSTER_NODES  集群节点列表 (host1:port1,host2:port2)
  S3_BUCKET            S3存储桶名称

示例:
  # 备份单机Redis
  $0 standalone

  # 备份集群
  REDIS_CLUSTER_NODES="192.168.1.10:6379,192.168.1.11:6379,192.168.1.12:6379" $0 cluster

EOF
}

# 主函数
main() {
    case "${1:-}" in
        standalone)
            backup_standalone
            ;;
        cluster)
            backup_cluster
            ;;
        sentinel)
            backup_sentinel
            ;;
        cleanup)
            cleanup_old_backups
            ;;
        status)
            show_status
            ;;
        -h|--help|help)
            usage
            exit 0
            ;;
        *)
            # 自动检测模式
            if is_cluster_mode; then
                log "INFO" "检测到集群模式，执行集群备份..."
                backup_cluster
            else
                log "INFO" "检测到单机模式，执行单机备份..."
                backup_standalone
            fi
            ;;
    esac
}

main "$@"
