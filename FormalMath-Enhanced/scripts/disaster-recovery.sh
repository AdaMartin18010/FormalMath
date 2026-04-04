#!/bin/bash
# ============================================
# FormalMath - 灾难恢复演练脚本
# 用于测试和验证灾难恢复流程
# ============================================

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 配置
PROJECT_DIR="/opt/formalmath-enhanced"
BACKUP_DIR="${PROJECT_DIR}/backups"
LOG_FILE="${PROJECT_DIR}/logs/disaster-recovery-$(date +%Y%m%d_%H%M%S).log"
DRY_RUN=false

# 日志函数
log() {
    echo -e "${BLUE}[$(date '+%Y-%m-%d %H:%M:%S')]${NC} $1" | tee -a "$LOG_FILE"
}

log_success() {
    echo -e "${GREEN}[$(date '+%Y-%m-%d %H:%M:%S')] ✓${NC} $1" | tee -a "$LOG_FILE"
}

log_error() {
    echo -e "${RED}[$(date '+%Y-%m-%d %H:%M:%S')] ✗${NC} $1" | tee -a "$LOG_FILE"
}

log_warning() {
    echo -e "${YELLOW}[$(date '+%Y-%m-%d %H:%M:%S')] ⚠${NC} $1" | tee -a "$LOG_FILE"
}

# 检查是否 Dry Run
check_dry_run() {
    if [ "$DRY_RUN" = true ]; then
        log_warning "[DRY RUN] 模拟执行: $1"
        return 0
    fi
    return 1
}

# 检查前置条件
precheck() {
    log "检查前置条件..."
    
    # 检查目录
    if [ ! -d "$PROJECT_DIR" ]; then
        log_error "项目目录不存在: $PROJECT_DIR"
        exit 1
    fi
    
    # 检查Docker
    if ! command -v docker &> /dev/null; then
        log_error "Docker未安装"
        exit 1
    fi
    
    # 检查备份目录
    if [ ! -d "$BACKUP_DIR" ]; then
        log_warning "备份目录不存在，创建中..."
        mkdir -p "$BACKUP_DIR"
    fi
    
    log_success "前置条件检查通过"
}

# 场景1: 完整系统故障恢复
scenario_total_failure() {
    log "=========================================="
    log "场景1: 完整系统故障恢复演练"
    log "=========================================="
    
    local scenario_start_time=$(date +%s)
    
    # 步骤1: 模拟系统完全故障
    log "步骤1: 停止所有服务..."
    if ! check_dry_run "停止所有Docker容器"; then
        cd "$PROJECT_DIR"
        docker-compose down --volumes --remove-orphans 2>&1 | tee -a "$LOG_FILE"
    fi
    
    # 步骤2: 模拟数据丢失
    log "步骤2: 模拟数据丢失..."
    if ! check_dry_run "删除数据卷"; then
        docker volume rm formalmath-enhanced_backend-data 2>/dev/null || true
        docker volume rm formalmath-enhanced_redis-data 2>/dev/null || true
    fi
    
    # 步骤3: 从备份恢复
    log "步骤3: 从备份恢复数据..."
    local latest_backup=$(ls -t "$BACKUP_DIR"/full-backup-*.tar.gz 2>/dev/null | head -1)
    
    if [ -z "$latest_backup" ]; then
        log_error "未找到可用的全量备份"
        return 1
    fi
    
    log "使用备份: $latest_backup"
    
    if ! check_dry_run "解压备份文件"; then
        cd "$BACKUP_DIR"
        tar -xzf "$latest_backup" -C /tmp/restore-$scenario_start_time/
        log_success "备份解压完成"
    fi
    
    # 步骤4: 重建服务
    log "步骤4: 重建服务..."
    if ! check_dry_run "启动Docker服务"; then
        cd "$PROJECT_DIR"
        docker-compose up -d
        sleep 10
    fi
    
    # 步骤5: 恢复数据
    log "步骤5: 恢复数据到容器..."
    if ! check_dry_run "恢复数据文件"; then
        docker cp /tmp/restore-$scenario_start_time/data/. formalmath-backend:/app/data/
        docker cp /tmp/restore-$scenario_start_time/redis/. formalmath-redis:/data/
    fi
    
    # 步骤6: 验证恢复
    log "步骤6: 验证服务恢复..."
    if ! check_dry_run "验证服务"; then
        sleep 5
        if curl -sf http://localhost/health > /dev/null; then
            log_success "服务恢复成功"
        else
            log_error "服务恢复失败"
            return 1
        fi
    fi
    
    # 计算RTO
    local scenario_end_time=$(date +%s)
    local rto=$((scenario_end_time - scenario_start_time))
    log "恢复时间目标(RTO): ${rto}秒"
    
    # 清理临时文件
    rm -rf /tmp/restore-$scenario_start_time/
    
    log_success "场景1完成"
    return 0
}

# 场景2: 数据库损坏恢复
scenario_database_corruption() {
    log "=========================================="
    log "场景2: 数据库损坏恢复演练"
    log "=========================================="
    
    local scenario_start_time=$(date +%s)
    
    # 步骤1: 备份当前数据
    log "步骤1: 创建临时备份..."
    if ! check_dry_run "创建临时备份"; then
        cd "$PROJECT_DIR"
        docker-compose exec -T backend tar czf /tmp/db-backup-pre-test.tar.gz /app/data/
    fi
    
    # 步骤2: 模拟数据库损坏
    log "步骤2: 模拟数据库损坏..."
    if ! check_dry_run "损坏数据库文件"; then
        docker-compose exec -T backend sh -c "echo 'CORRUPTED' > /app/data/formalmath.db"
    fi
    
    # 步骤3: 检测损坏
    log "步骤3: 检测数据损坏..."
    if ! check_dry_run "检测健康状态"; then
        if curl -sf http://localhost/health > /dev/null; then
            log_warning "健康检查通过，可能未检测到损坏"
        else
            log "检测到服务异常，开始恢复流程"
        fi
    fi
    
    # 步骤4: 停止服务并恢复
    log "步骤4: 恢复数据库..."
    if ! check_dry_run "恢复数据库"; then
        docker-compose stop backend
        docker cp /tmp/db-backup-pre-test.tar.gz formalmath-backend:/tmp/
        docker-compose exec -T backend tar xzf /tmp/db-backup-pre-test.tar.gz -C /
        docker-compose start backend
        sleep 5
    fi
    
    # 步骤5: 验证
    log "步骤5: 验证数据库恢复..."
    if ! check_dry_run "验证恢复"; then
        if curl -sf http://localhost/api/v1/health > /dev/null; then
            log_success "数据库恢复成功"
        else
            log_error "数据库恢复失败"
            return 1
        fi
    fi
    
    # 清理
    rm -f /tmp/db-backup-pre-test.tar.gz
    
    local scenario_end_time=$(date +%s)
    local rto=$((scenario_end_time - scenario_start_time))
    log "恢复时间: ${rto}秒"
    
    log_success "场景2完成"
    return 0
}

# 场景3: 服务降级演练
scenario_service_degradation() {
    log "=========================================="
    log "场景3: 服务降级演练"
    log "=========================================="
    
    # 步骤1: 模拟后端服务故障
    log "步骤1: 模拟后端服务故障..."
    if ! check_dry_run "停止后端服务"; then
        docker-compose stop backend celery-worker
        sleep 2
    fi
    
    # 步骤2: 验证降级模式
    log "步骤2: 验证降级模式..."
    if ! check_dry_run "检查静态页面访问"; then
        if curl -sf http://localhost/ > /dev/null; then
            log_success "静态页面仍可访问（降级成功）"
        else
            log_error "静态页面无法访问"
        fi
    fi
    
    # 步骤3: 恢复服务
    log "步骤3: 恢复后端服务..."
    if ! check_dry_run "启动后端服务"; then
        docker-compose start backend celery-worker
        sleep 5
    fi
    
    # 步骤4: 验证完全恢复
    log "步骤4: 验证完全恢复..."
    if ! check_dry_run "完整验证"; then
        if curl -sf http://localhost/api/v1/health > /dev/null; then
            log_success "服务完全恢复"
        else
            log_error "服务恢复失败"
            return 1
        fi
    fi
    
    log_success "场景3完成"
    return 0
}

# 场景4: Redis故障恢复
scenario_redis_failure() {
    log "=========================================="
    log "场景4: Redis故障恢复演练"
    log "=========================================="
    
    local scenario_start_time=$(date +%s)
    
    # 步骤1: 模拟Redis故障
    log "步骤1: 模拟Redis故障..."
    if ! check_dry_run "停止Redis"; then
        docker-compose stop redis
        sleep 2
    fi
    
    # 步骤2: 验证应用行为
    log "步骤2: 验证应用降级行为..."
    if ! check_dry_run "检查API响应"; then
        # 应用应该在没有Redis的情况下继续工作（降级模式）
        if curl -sf http://localhost/api/v1/health > /dev/null; then
            log_success "应用在Redis故障下仍可工作"
        else
            log_warning "应用依赖Redis，考虑实现降级策略"
        fi
    fi
    
    # 步骤3: 恢复Redis
    log "步骤3: 恢复Redis服务..."
    if ! check_dry_run "启动Redis"; then
        docker-compose start redis
        sleep 5
    fi
    
    # 步骤4: 验证缓存恢复
    log "步骤4: 验证缓存恢复..."
    if ! check_dry_run "检查Redis连接"; then
        docker-compose exec -T redis redis-cli ping | grep -q "PONG"
        if [ $? -eq 0 ]; then
            log_success "Redis恢复成功"
        else
            log_error "Redis恢复失败"
            return 1
        fi
    fi
    
    local scenario_end_time=$(date +%s)
    local rto=$((scenario_end_time - scenario_start_time))
    log "恢复时间: ${rto}秒"
    
    log_success "场景4完成"
    return 0
}

# 生成报告
generate_report() {
    log "=========================================="
    log "生成灾难恢复演练报告"
    log "=========================================="
    
    local report_file="${PROJECT_DIR}/reports/dr-report-$(date +%Y%m%d_%H%M%S).md"
    mkdir -p "$(dirname "$report_file")"
    
    cat > "$report_file" << EOF
# FormalMath 灾难恢复演练报告

**演练时间**: $(date '+%Y-%m-%d %H:%M:%S')  
**执行用户**: $(whoami)  
**日志文件**: $LOG_FILE

## 执行摘要

本次灾难恢复演练测试了以下场景：
1. 完整系统故障恢复
2. 数据库损坏恢复
3. 服务降级演练
4. Redis故障恢复

## 详细结果

### RTO (恢复时间目标) 统计

| 场景 | 目标RTO | 实际RTO | 状态 |
|------|---------|---------|------|
| 完整系统故障 | < 30分钟 | 待填充 | 待填充 |
| 数据库损坏 | < 15分钟 | 待填充 | 待填充 |
| 服务降级 | < 5分钟 | 待填充 | 待填充 |
| Redis故障 | < 5分钟 | 待填充 | 待填充 |

## 发现的问题

（根据实际执行填写）

## 改进建议

（根据实际执行填写）

## 附录

- 完整日志: $LOG_FILE
EOF

    log_success "报告已生成: $report_file"
}

# 使用说明
usage() {
    cat << EOF
FormalMath 灾难恢复演练脚本

用法: $0 [选项] [场景]

选项:
    -h, --help          显示帮助信息
    -d, --dry-run       模拟运行，不实际执行操作
    -a, --all           执行所有场景
    
场景:
    total               完整系统故障恢复
    database            数据库损坏恢复
    degradation         服务降级演练
    redis               Redis故障恢复
    report              生成报告

示例:
    $0 --dry-run total      # 模拟完整系统故障恢复
    $0 --all                # 执行所有场景
    $0 database             # 只执行数据库恢复场景
EOF
}

# 主函数
main() {
    local run_all=false
    local scenarios=()
    
    # 解析参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                usage
                exit 0
                ;;
            -d|--dry-run)
                DRY_RUN=true
                shift
                ;;
            -a|--all)
                run_all=true
                shift
                ;;
            total|database|degradation|redis|report)
                scenarios+=("$1")
                shift
                ;;
            *)
                log_error "未知参数: $1"
                usage
                exit 1
                ;;
        esac
    done
    
    # 初始化
    mkdir -p "$(dirname "$LOG_FILE")"
    log "灾难恢复演练开始"
    log "模式: $([ "$DRY_RUN" = true ] && echo '模拟运行' || echo '实际执行')"
    
    # 前置检查
    precheck
    
    # 执行场景
    local failed=0
    
    if [ "$run_all" = true ] || [[ " ${scenarios[*]} " =~ " total " ]]; then
        scenario_total_failure || ((failed++))
    fi
    
    if [ "$run_all" = true ] || [[ " ${scenarios[*]} " =~ " database " ]]; then
        scenario_database_corruption || ((failed++))
    fi
    
    if [ "$run_all" = true ] || [[ " ${scenarios[*]} " =~ " degradation " ]]; then
        scenario_service_degradation || ((failed++))
    fi
    
    if [ "$run_all" = true ] || [[ " ${scenarios[*]} " =~ " redis " ]]; then
        scenario_redis_failure || ((failed++))
    fi
    
    if [[ " ${scenarios[*]} " =~ " report " ]]; then
        generate_report
    fi
    
    # 总结
    log "=========================================="
    if [ $failed -eq 0 ]; then
        log_success "所有场景执行成功"
    else
        log_error "$failed 个场景执行失败"
    fi
    log "详细日志: $LOG_FILE"
    log "=========================================="
    
    exit $failed
}

# 执行主函数
main "$@"
