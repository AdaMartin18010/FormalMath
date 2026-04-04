#!/bin/bash
# ============================================
# FormalMath - 生产环境部署脚本
# 支持Docker Compose和Kubernetes部署
# ============================================

set -euo pipefail

# 配置
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
DEPLOY_ENV="${DEPLOY_ENV:-production}"
VERSION="${VERSION:-latest}"
NAMESPACE="${NAMESPACE:-formalmath-prod}"

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 日志函数
log_info() {
    echo -e "${BLUE}[INFO]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $(date '+%Y-%m-%d %H:%M:%S') - $1"
}

# 显示帮助
show_help() {
    cat << EOF
FormalMath 生产环境部署脚本

用法: $0 [选项] <命令>

命令:
    deploy          执行部署
    rollback        回滚到上一个版本
    status          查看部署状态
    health          健康检查
    logs            查看日志
    scale           扩缩容
    maintenance     维护模式

选项:
    -e, --env       部署环境 (production/staging) [默认: production]
    -v, --version   部署版本 [默认: latest]
    -n, --namespace Kubernetes命名空间 [默认: formalmath-prod]
    -t, --target    部署目标 (docker/k8s) [默认: docker]
    -h, --help      显示帮助

示例:
    $0 deploy -e production -v v2.0.0
    $0 rollback -e production
    $0 status
    $0 health
    $0 logs -s backend
    $0 scale -s backend -r 5
    $0 maintenance on

EOF
}

# 检查前置条件
check_prerequisites() {
    log_info "检查前置条件..."
    
    # 检查Docker
    if ! command -v docker &> /dev/null; then
        log_error "Docker未安装"
        exit 1
    fi
    
    # 检查Docker Compose
    if ! command -v docker-compose &> /dev/null; then
        log_error "Docker Compose未安装"
        exit 1
    fi
    
    # 检查环境变量文件
    if [[ ! -f "$PROJECT_ROOT/production/.env.production" ]]; then
        log_warn "未找到.env.production文件，使用模板创建..."
        cp "$PROJECT_ROOT/production/.env.production.template" "$PROJECT_ROOT/production/.env.production"
        log_warn "请编辑 $PROJECT_ROOT/production/.env.production 文件并填写实际值"
        exit 1
    fi
    
    log_success "前置条件检查通过"
}

# 构建镜像
build_images() {
    log_info "构建Docker镜像..."
    
    export VERSION
    
    # 构建后端镜像
    log_info "构建后端镜像..."
    docker build \
        -t formalmath/backend:${VERSION} \
        -f "$PROJECT_ROOT/../FormalMath-Enhanced/Dockerfile.backend.optimized" \
        --target production \
        "$PROJECT_ROOT/../FormalMath-Enhanced"
    
    # 构建前端镜像
    log_info "构建前端镜像..."
    docker build \
        -t formalmath/frontend:${VERSION} \
        -f "$PROJECT_ROOT/../FormalMath-Enhanced/Dockerfile.frontend.optimized" \
        --target production \
        "$PROJECT_ROOT/../FormalMath-Enhanced"
    
    log_success "镜像构建完成"
}

# 部署到Docker Compose
deploy_docker() {
    log_info "开始Docker Compose部署..."
    
    cd "$PROJECT_ROOT/../FormalMath-Enhanced"
    
    # 加载环境变量
    export $(grep -v '^#' "$PROJECT_ROOT/production/.env.production" | xargs)
    
    # 拉取最新镜像
    log_info "拉取最新镜像..."
    docker-compose -f docker-compose.production.yml pull
    
    # 执行数据库迁移
    log_info "执行数据库迁移..."
    docker-compose -f docker-compose.production.yml run --rm backend alembic upgrade head || true
    
    # 滚动更新
    log_info "开始滚动更新..."
    docker-compose -f docker-compose.production.yml up -d --no-deps --build backend
    sleep 10
    docker-compose -f docker-compose.production.yml up -d --no-deps --build frontend
    
    # 等待服务启动
    log_info "等待服务启动..."
    sleep 30
    
    # 健康检查
    if ! health_check; then
        log_error "健康检查失败，执行回滚..."
        rollback_docker
        exit 1
    fi
    
    log_success "Docker Compose部署完成"
}

# 部署到Kubernetes
deploy_k8s() {
    log_info "开始Kubernetes部署..."
    
    # 检查kubectl
    if ! command -v kubectl &> /dev/null; then
        log_error "kubectl未安装"
        exit 1
    fi
    
    # 更新镜像标签
    log_info "更新镜像标签..."
    kubectl set image deployment/backend-deployment backend=formalmath/backend:${VERSION} -n ${NAMESPACE}
    kubectl set image deployment/frontend-deployment frontend=formalmath/frontend:${VERSION} -n ${NAMESPACE}
    
    # 等待滚动更新完成
    log_info "等待滚动更新完成..."
    kubectl rollout status deployment/backend-deployment -n ${NAMESPACE} --timeout=300s
    kubectl rollout status deployment/frontend-deployment -n ${NAMESPACE} --timeout=300s
    
    # 验证部署
    if ! health_check; then
        log_error "健康检查失败，执行回滚..."
        rollback_k8s
        exit 1
    fi
    
    log_success "Kubernetes部署完成"
}

# 回滚Docker Compose
deploy_rollback_docker() {
    log_info "开始Docker Compose回滚..."
    
    cd "$PROJECT_ROOT/../FormalMath-Enhanced"
    
    # 回滚到上一个版本
    docker-compose -f docker-compose.production.yml down
    docker-compose -f docker-compose.production.yml up -d
    
    log_success "Docker Compose回滚完成"
}

# 回滚Kubernetes
deploy_rollback_k8s() {
    log_info "开始Kubernetes回滚..."
    
    # 回滚后端
    kubectl rollout undo deployment/backend-deployment -n ${NAMESPACE}
    kubectl rollout status deployment/backend-deployment -n ${NAMESPACE} --timeout=300s
    
    # 回滚前端
    kubectl rollout undo deployment/frontend-deployment -n ${NAMESPACE}
    kubectl rollout status deployment/frontend-deployment -n ${NAMESPACE} --timeout=300s
    
    log_success "Kubernetes回滚完成"
}

# 健康检查
health_check() {
    log_info "执行健康检查..."
    
    local max_retries=10
    local retry=0
    local backend_healthy=false
    local frontend_healthy=false
    
    while [[ $retry -lt $max_retries ]]; do
        # 检查后端
        if curl -sf http://localhost:8000/health > /dev/null 2>&1; then
            backend_healthy=true
            log_success "后端服务健康"
        fi
        
        # 检查前端
        if curl -sf http://localhost:80/ > /dev/null 2>&1; then
            frontend_healthy=true
            log_success "前端服务健康"
        fi
        
        if [[ "$backend_healthy" == true && "$frontend_healthy" == true ]]; then
            log_success "所有服务健康检查通过"
            return 0
        fi
        
        retry=$((retry + 1))
        log_info "等待服务启动... ($retry/$max_retries)"
        sleep 10
    done
    
    log_error "健康检查失败"
    return 1
}

# 查看状态
show_status() {
    log_info "查看部署状态..."
    
    cd "$PROJECT_ROOT/../FormalMath-Enhanced"
    
    echo "=== Docker容器状态 ==="
    docker-compose -f docker-compose.production.yml ps
    
    echo ""
    echo "=== 资源使用情况 ==="
    docker stats --no-stream --format "table {{.Name}}\t{{.CPUPerc}}\t{{.MemUsage}}\t{{.NetIO}}\t{{.BlockIO}}"
}

# 查看日志
show_logs() {
    local service="${1:-}"
    
    cd "$PROJECT_ROOT/../FormalMath-Enhanced"
    
    if [[ -n "$service" ]]; then
        docker-compose -f docker-compose.production.yml logs -f "$service"
    else
        docker-compose -f docker-compose.production.yml logs -f
    fi
}

# 扩缩容
scale_service() {
    local service="${1:-}"
    local replicas="${2:-}"
    
    if [[ -z "$service" || -z "$replicas" ]]; then
        log_error "请指定服务和副本数"
        echo "用法: $0 scale -s <service> -r <replicas>"
        exit 1
    fi
    
    cd "$PROJECT_ROOT/../FormalMath-Enhanced"
    
    log_info "扩容 $service 到 $replicas 个副本..."
    docker-compose -f docker-compose.production.yml up -d --scale "$service=$replicas"
    
    log_success "扩容完成"
}

# 维护模式
maintenance_mode() {
    local action="${1:-off}"
    
    cd "$PROJECT_ROOT/../FormalMath-Enhanced"
    
    if [[ "$action" == "on" ]]; then
        log_info "开启维护模式..."
        docker-compose -f docker-compose.production.yml -f docker-compose.maintenance.yml up -d
        log_success "维护模式已开启"
    else
        log_info "关闭维护模式..."
        docker-compose -f docker-compose.production.yml up -d
        log_success "维护模式已关闭"
    fi
}

# 主函数
main() {
    local command=""
    local target="docker"
    local service=""
    local replicas=""
    
    # 解析参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            deploy|rollback|status|health|logs|scale|maintenance)
                command="$1"
                shift
                ;;
            -e|--env)
                DEPLOY_ENV="$2"
                shift 2
                ;;
            -v|--version)
                VERSION="$2"
                shift 2
                ;;
            -n|--namespace)
                NAMESPACE="$2"
                shift 2
                ;;
            -t|--target)
                target="$2"
                shift 2
                ;;
            -s|--service)
                service="$2"
                shift 2
                ;;
            -r|--replicas)
                replicas="$2"
                shift 2
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            *)
                log_error "未知选项: $1"
                show_help
                exit 1
                ;;
        esac
    done
    
    # 检查命令
    if [[ -z "$command" ]]; then
        log_error "请指定命令"
        show_help
        exit 1
    fi
    
    # 执行命令
    case $command in
        deploy)
            check_prerequisites
            build_images
            if [[ "$target" == "k8s" ]]; then
                deploy_k8s
            else
                deploy_docker
            fi
            ;;
        rollback)
            if [[ "$target" == "k8s" ]]; then
                deploy_rollback_k8s
            else
                deploy_rollback_docker
            fi
            ;;
        status)
            show_status
            ;;
        health)
            health_check
            ;;
        logs)
            show_logs "$service"
            ;;
        scale)
            scale_service "$service" "$replicas"
            ;;
        maintenance)
            maintenance_mode "${service:-off}"
            ;;
        *)
            log_error "未知命令: $command"
            show_help
            exit 1
            ;;
    esac
}

# 运行主函数
main "$@"
