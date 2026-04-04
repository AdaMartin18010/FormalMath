#!/bin/bash
# FormalMath - 生产环境部署脚本

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# 配置
COMPOSE_FILE="docker-compose.production.yml"
ENV_FILE="api/.env"
BACKUP_DIR="backups/$(date +%Y%m%d_%H%M%S)"

# 打印带颜色的消息
print_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 显示帮助
show_help() {
    cat << EOF
FormalMath 部署脚本

用法: $0 [选项] [命令]

命令:
    start       启动所有服务
    stop        停止所有服务
    restart     重启所有服务
    update      更新并重新部署
    backup      备份数据
    logs        查看日志
    status      查看服务状态
    clean       清理未使用的资源

选项:
    -h, --help  显示帮助信息
    -m, --monitoring  包含监控服务

示例:
    $0 start           # 启动基本服务
    $0 start -m        # 启动包含监控的服务
    $0 update          # 更新部署
    $0 backup          # 备份数据
EOF
}

# 检查环境
check_environment() {
    print_info "检查环境..."
    
    # 检查Docker
    if ! command -v docker &> /dev/null; then
        print_error "Docker 未安装"
        exit 1
    fi
    
    # 检查Docker Compose
    if ! command -v docker-compose &> /dev/null; then
        print_error "Docker Compose 未安装"
        exit 1
    fi
    
    # 检查.env文件
    if [ ! -f "$ENV_FILE" ]; then
        print_warning "环境文件 $ENV_FILE 不存在，将使用默认配置"
        if [ -f "${ENV_FILE}.example" ]; then
            cp "${ENV_FILE}.example" "$ENV_FILE"
            print_info "已从模板创建 $ENV_FILE"
        fi
    fi
    
    print_success "环境检查通过"
}

# 启动服务
start_services() {
    local with_monitoring=$1
    
    print_info "启动服务..."
    
    if [ "$with_monitoring" = true ]; then
        docker-compose -f "$COMPOSE_FILE" --profile monitoring up -d
    else
        docker-compose -f "$COMPOSE_FILE" up -d
    fi
    
    print_info "等待服务启动..."
    sleep 10
    
    # 健康检查
    if ./scripts/health-check.sh; then
        print_success "服务启动成功"
        print_info "访问: http://localhost"
        print_info "API文档: http://localhost/docs"
        
        if [ "$with_monitoring" = true ]; then
            print_info "Grafana: http://localhost:3000"
            print_info "Prometheus: http://localhost:9090"
        fi
    else
        print_error "服务启动失败，请检查日志"
        docker-compose logs
        exit 1
    fi
}

# 停止服务
stop_services() {
    print_info "停止服务..."
    docker-compose -f "$COMPOSE_FILE" --profile monitoring down
    print_success "服务已停止"
}

# 重启服务
restart_services() {
    print_info "重启服务..."
    docker-compose -f "$COMPOSE_FILE" restart
    print_success "服务已重启"
}

# 更新部署
update_deployment() {
    print_info "更新部署..."
    
    # 备份数据
    backup_data
    
    # 拉取最新代码（如果在git仓库中）
    if [ -d ".git" ]; then
        print_info "拉取最新代码..."
        git pull origin main
    fi
    
    # 重新构建
    print_info "重新构建镜像..."
    docker-compose -f "$COMPOSE_FILE" build --no-cache
    
    # 滚动更新
    print_info "滚动更新服务..."
    docker-compose -f "$COMPOSE_FILE" up -d --no-deps --build
    
    print_success "更新完成"
}

# 备份数据
backup_data() {
    print_info "备份数据..."
    
    mkdir -p "$BACKUP_DIR"
    
    # 备份数据库
    if docker-compose exec -T backend test -f /app/data/formalmath.db; then
        docker-compose exec -T backend cp /app/data/formalmath.db "/app/data/formalmath.db.backup.$(date +%Y%m%d)"
        docker cp "formalmath-backend:/app/data/formalmath.db.backup.$(date +%Y%m%d)" "$BACKUP_DIR/"
        print_success "数据库已备份到 $BACKUP_DIR"
    fi
    
    # 备份Redis
    docker-compose exec -T redis redis-cli SAVE || true
    if docker cp "formalmath-redis:/data/dump.rdb" "$BACKUP_DIR/redis-$(date +%Y%m%d).rdb"; then
        print_success "Redis数据已备份到 $BACKUP_DIR"
    fi
}

# 查看日志
show_logs() {
    local service=$1
    if [ -n "$service" ]; then
        docker-compose logs -f "$service"
    else
        docker-compose logs -f
    fi
}

# 查看状态
show_status() {
    echo "========================================"
    echo "容器状态"
    echo "========================================"
    docker-compose ps
    
    echo ""
    echo "========================================"
    echo "资源使用"
    echo "========================================"
    docker stats --no-stream --format "table {{.Container}}\t{{.CPUPerc}}\t{{.MemUsage}}\t{{.MemPerc}}"
}

# 清理资源
cleanup() {
    print_warning "这将清理未使用的Docker资源"
    read -p "确定继续? (y/N) " -n 1 -r
    echo
    
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        print_info "清理未使用的容器..."
        docker container prune -f
        
        print_info "清理未使用的镜像..."
        docker image prune -f
        
        print_info "清理未使用的卷..."
        docker volume prune -f
        
        print_info "清理构建缓存..."
        docker builder prune -f
        
        print_success "清理完成"
    fi
}

# 主程序
main() {
    local command=""
    local with_monitoring=false
    
    # 解析参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                show_help
                exit 0
                ;;
            -m|--monitoring)
                with_monitoring=true
                shift
                ;;
            start|stop|restart|update|backup|logs|status|clean)
                command=$1
                shift
                ;;
            *)
                print_error "未知选项: $1"
                show_help
                exit 1
                ;;
        esac
    done
    
    # 执行命令
    case $command in
        start)
            check_environment
            start_services "$with_monitoring"
            ;;
        stop)
            stop_services
            ;;
        restart)
            restart_services
            ;;
        update)
            check_environment
            update_deployment
            ;;
        backup)
            backup_data
            ;;
        logs)
            show_logs "$2"
            ;;
        status)
            show_status
            ;;
        clean)
            cleanup
            ;;
        *)
            show_help
            exit 1
            ;;
    esac
}

main "$@"
