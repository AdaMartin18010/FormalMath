#!/bin/bash
# ============================================
# FormalMath - 数据库迁移脚本
# 支持SQLite和PostgreSQL迁移
# ============================================

set -euo pipefail

# 配置
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
LOG_FILE="${PROJECT_ROOT}/logs/database-migrate.log"
BACKUP_DIR="${PROJECT_ROOT}/backups/migrations"

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
FormalMath 数据库迁移脚本

用法: $0 [选项] [命令]

命令:
    init        初始化数据库
    migrate     执行迁移
    rollback    回滚迁移
    status      查看迁移状态
    backup      备份数据库
    restore     恢复数据库
    seed        填充测试数据
    reset       重置数据库（危险！）

选项:
    -e, --env           环境文件路径 (默认: .env.production)
    -v, --version       指定迁移版本
    -f, --force         强制执行（跳过确认）
    -h, --help          显示帮助

示例:
    $0 init
    $0 migrate
    $0 rollback -v 20240101000000
    $0 backup
EOF
}

# 初始化
init() {
    info "初始化数据库..."
    mkdir -p "$BACKUP_DIR" "$(dirname "$LOG_FILE")"
    
    # 检查Docker Compose运行状态
    if ! docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" ps | grep -q "backend"; then
        warn "后端服务未运行，请先启动服务"
        exit 1
    fi
    
    # 执行初始化命令
    docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" exec -T backend \
        python -c "
import asyncio
import sys
sys.path.insert(0, '/app')
from database import init_db
asyncio.run(init_db())
print('数据库初始化完成')
"
    
    success "数据库初始化完成"
}

# 执行迁移
migrate() {
    local version="${1:-latest}"
    info "执行数据库迁移 (目标版本: $version)..."
    
    # 备份当前数据库
    backup_database
    
    # 执行迁移
    docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" exec -T backend \
        python -c "
import asyncio
import sys
sys.path.insert(0, '/app')
from migrations import run_migrations
asyncio.run(run_migrations('$version'))
print('迁移完成')
"
    
    success "数据库迁移完成"
}

# 回滚迁移
rollback() {
    local version="${1:-}"
    
    if [[ -z "$version" ]]; then
        error "请指定回滚目标版本: $0 rollback -v <version>"
        exit 1
    fi
    
    warn "即将回滚到版本: $version"
    if [[ "$FORCE" != true ]]; then
        read -p "确定要继续吗? (yes/no) " confirm
        if [[ "$confirm" != "yes" ]]; then
            info "操作已取消"
            return 0
        fi
    fi
    
    info "回滚数据库迁移..."
    
    # 备份当前数据库
    backup_database
    
    # 执行回滚
    docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" exec -T backend \
        python -c "
import asyncio
import sys
sys.path.insert(0, '/app')
from migrations import rollback_migrations
asyncio.run(rollback_migrations('$version'))
print('回滚完成')
"
    
    success "数据库回滚完成"
}

# 查看迁移状态
status() {
    info "查看数据库迁移状态..."
    
    docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" exec -T backend \
        python -c "
import asyncio
import sys
sys.path.insert(0, '/app')
from migrations import show_migration_status
asyncio.run(show_migration_status())
"
}

# 备份数据库
backup_database() {
    local timestamp=$(date +%Y%m%d_%H%M%S)
    local backup_file="${BACKUP_DIR}/backup_${timestamp}.sql"
    
    info "备份数据库..."
    mkdir -p "$BACKUP_DIR"
    
    # 检测数据库类型并执行相应备份
    docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" exec -T backend \
        python -c "
import asyncio
import sys
import os
sys.path.insert(0, '/app')
from database import get_database_url

async def backup():
    db_url = await get_database_url()
    if 'postgresql' in db_url:
        print('PostgreSQL备份需要使用pg_dump')
    elif 'sqlite' in db_url:
        import shutil
        db_path = db_url.replace('sqlite:///', '/app/')
        if os.path.exists(db_path):
            backup_path = '/app/data/backup_${timestamp}.db'
            shutil.copy2(db_path, backup_path)
            print(f'SQLite数据库已备份到: {backup_path}')
        else:
            print('数据库文件不存在')
    else:
        print('不支持的数据库类型')

asyncio.run(backup())
"
    
    # 复制备份到主机
    docker cp "formalmath-backend:/app/data/backup_${timestamp}.db" "$backup_file" 2>/dev/null || true
    
    success "数据库备份完成: $backup_file"
}

# 恢复数据库
restore_database() {
    local backup_file="${1:-}"
    
    if [[ -z "$backup_file" ]]; then
        # 列出可用的备份
        info "可用的备份文件:"
        ls -la "$BACKUP_DIR"/*.db 2>/dev/null || {
            warn "没有找到备份文件"
            exit 1
        }
        
        read -p "请输入要恢复的备份文件名: " backup_file
        backup_file="$BACKUP_DIR/$backup_file"
    fi
    
    if [[ ! -f "$backup_file" ]]; then
        error "备份文件不存在: $backup_file"
        exit 1
    fi
    
    warn "即将恢复数据库，这将覆盖当前数据！"
    if [[ "$FORCE" != true ]]; then
        read -p "确定要继续吗? (yes/no) " confirm
        if [[ "$confirm" != "yes" ]]; then
            info "操作已取消"
            return 0
        fi
    fi
    
    info "恢复数据库: $backup_file"
    
    # 复制备份到容器
    docker cp "$backup_file" "formalmath-backend:/app/data/restore_temp.db"
    
    # 执行恢复
    docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" exec -T backend \
        python -c "
import asyncio
import sys
import os
import shutil
sys.path.insert(0, '/app')

async def restore():
    db_path = '/app/data/formalmath.db'
    backup_path = '/app/data/restore_temp.db'
    
    if os.path.exists(backup_path):
        # 创建当前数据库的临时备份
        if os.path.exists(db_path):
            shutil.copy2(db_path, db_path + '.before_restore')
        # 恢复备份
        shutil.copy2(backup_path, db_path)
        os.remove(backup_path)
        print('数据库恢复完成')
    else:
        print('恢复文件不存在')

asyncio.run(restore())
"
    
    success "数据库恢复完成"
}

# 填充测试数据
seed() {
    info "填充测试数据..."
    
    docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" exec -T backend \
        python -c "
import asyncio
import sys
sys.path.insert(0, '/app')
from seed_data import seed_database
asyncio.run(seed_database())
print('测试数据填充完成')
"
    
    success "测试数据填充完成"
}

# 重置数据库（危险操作）
reset() {
    warn "这将删除所有数据并重置数据库！"
    if [[ "$FORCE" != true ]]; then
        read -p "请输入 'RESET' 确认: " confirm
        if [[ "$confirm" != "RESET" ]]; then
            info "操作已取消"
            return 0
        fi
    fi
    
    # 先备份
    backup_database
    
    info "重置数据库..."
    
    docker-compose -f "$PROJECT_ROOT/docker-compose.production.yml" exec -T backend \
        python -c "
import asyncio
import sys
import os
sys.path.insert(0, '/app')

async def reset():
    db_path = '/app/data/formalmath.db'
    if os.path.exists(db_path):
        os.remove(db_path)
        print('数据库已删除')
    
    from database import init_db
    await init_db()
    print('数据库已重新初始化')

asyncio.run(reset())
"
    
    success "数据库重置完成"
}

# 设置自动备份定时任务
setup_backup_cron() {
    info "设置自动备份定时任务..."
    
    local cron_job="0 2 * * * $SCRIPT_DIR/database-migrate.sh backup >> $LOG_FILE 2>&1"
    
    if crontab -l 2>/dev/null | grep -q "$SCRIPT_DIR/database-migrate.sh backup"; then
        info "自动备份任务已存在"
    else
        (crontab -l 2>/dev/null; echo "$cron_job") | crontab -
        success "自动备份任务已添加: 每天凌晨2点执行"
    fi
    
    # 添加清理旧备份任务（每周执行）
    local cleanup_job="0 3 * * 0 find $BACKUP_DIR -name 'backup_*.sql' -mtime +30 -delete"
    if ! crontab -l 2>/dev/null | grep -q "find $BACKUP_DIR"; then
        (crontab -l 2>/dev/null; echo "$cleanup_job") | crontab -
        success "备份清理任务已添加: 每周日凌晨3点清理30天前的备份"
    fi
}

# 主函数
main() {
    local command=""
    local version=""
    local env_file=".env.production"
    FORCE=false
    
    # 解析参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            -e|--env)
                env_file="$2"
                shift 2
                ;;
            -v|--version)
                version="$2"
                shift 2
                ;;
            -f|--force)
                FORCE=true
                shift
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            init|migrate|rollback|status|backup|restore|seed|reset)
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
    
    # 创建必要的目录
    mkdir -p "$BACKUP_DIR" "$(dirname "$LOG_FILE")"
    
    # 加载环境变量
    if [[ -f "$PROJECT_ROOT/$env_file" ]]; then
        export $(grep -v '^#' "$PROJECT_ROOT/$env_file" | xargs)
    fi
    
    # 执行命令
    case $command in
        init)
            init
            ;;
        migrate)
            migrate "$version"
            ;;
        rollback)
            rollback "$version"
            ;;
        status)
            status
            ;;
        backup)
            backup_database
            setup_backup_cron
            ;;
        restore)
            restore_database "$version"
            ;;
        seed)
            seed
            ;;
        reset)
            reset
            ;;
        *)
            show_help
            exit 1
            ;;
    esac
}

main "$@"
