#!/bin/bash
# ============================================
# FormalMath - 生产环境回滚脚本
# 支持快速回滚到指定版本
# ============================================

set -euo pipefail

# 配置
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
NAMESPACE="${NAMESPACE:-formalmath-prod}"

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

# 显示帮助
show_help() {
    cat << EOF
FormalMath 生产环境回滚脚本

用法: $0 [选项] <命令>

命令:
    list            列出可回滚的版本
    rollback        回滚到上一个版本
    revert          回滚到指定版本
    status          查看回滚历史

选项:
    -v, --version   指定回滚版本
    -n, --namespace Kubernetes命名空间 [默认: formalmath-prod]
    -t, --target    回滚目标 (docker/k8s) [默认: docker]
    -f, --force     强制回滚（跳过确认）
    -h, --help      显示帮助

示例:
    $0 list
    $0 rollback
    $0 revert -v v1.9.0
    $0 status

EOF
}

# 列出可回滚版本
list_versions() {
    log_info "列出可回滚的版本..."
    
    if [[ "$TARGET" == "k8s" ]]; then
        echo "=== Kubernetes 部署历史 ==="
        kubectl rollout history deployment/backend-deployment -n ${NAMESPACE}
        echo ""
        kubectl rollout history deployment/frontend-deployment -n ${NAMESPACE}
    else
        echo "=== Docker 镜像历史 ==="
        docker images --format "table {{.Repository}}\t{{.Tag}}\t{{.CreatedAt}}\t{{.Size}}" | grep formalmath
    fi
}

# 回滚到上一个版本
rollback_previous() {
    log_warn "即将回滚到上一个版本..."
    
    if [[ "$FORCE" != "true" ]]; then
        read -p "确认回滚? [y/N] " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            log_info "取消回滚"
            exit 0
        fi
    fi
    
    if [[ "$TARGET" == "k8s" ]]; then
        rollback_k8s_previous
    else
        rollback_docker_previous
    fi
}

# Kubernetes回滚到上一个版本
rollback_k8s_previous() {
    log_info "开始Kubernetes回滚..."
    
    # 保存当前版本信息
    CURRENT_BACKEND_IMAGE=$(kubectl get deployment backend-deployment -n ${NAMESPACE} -o jsonpath='{.spec.template.spec.containers[0].image}')
    CURRENT_FRONTEND_IMAGE=$(kubectl get deployment frontend-deployment -n ${NAMESPACE} -o jsonpath='{.spec.template.spec.containers[0].image}')
    
    log_info "当前后端镜像: $CURRENT_BACKEND_IMAGE"
    log_info "当前前端镜像: $CURRENT_FRONTEND_IMAGE"
    
    # 执行回滚
    log_info "回滚后端服务..."
    kubectl rollout undo deployment/backend-deployment -n ${NAMESPACE}
    kubectl rollout status deployment/backend-deployment -n ${NAMESPACE} --timeout=300s
    
    log_info "回滚前端服务..."
    kubectl rollout undo deployment/frontend-deployment -n ${NAMESPACE}
    kubectl rollout status deployment/frontend-deployment -n ${NAMESPACE} --timeout=300s
    
    # 验证回滚
    NEW_BACKEND_IMAGE=$(kubectl get deployment backend-deployment -n ${NAMESPACE} -o jsonpath='{.spec.template.spec.containers[0].image}')
    NEW_FRONTEND_IMAGE=$(kubectl get deployment frontend-deployment -n ${NAMESPACE} -o jsonpath='{.spec.template.spec.containers[0].image}')
    
    log_success "回滚完成"
    log_info "回滚后后端镜像: $NEW_BACKEND_IMAGE"
    log_info "回滚后前端镜像: $NEW_FRONTEND_IMAGE"
    
    # 健康检查
    sleep 10
    if ! health_check; then
        log_error "回滚后健康检查失败，可能需要手动干预"
        exit 1
    fi
}

# Docker回滚到上一个版本
rollback_docker_previous() {
    log_info "开始Docker回滚..."
    
    cd "$PROJECT_ROOT/../FormalMath-Enhanced"
    
    # 停止当前服务
    log_info "停止当前服务..."
    docker-compose -f docker-compose.production.yml down
    
    # 使用上一个镜像版本
    log_info "启动上一个版本..."
    docker-compose -f docker-compose.production.yml up -d
    
    # 等待服务启动
    sleep 30
    
    # 健康检查
    if ! health_check; then
        log_error "回滚后健康检查失败"
        exit 1
    fi
    
    log_success "Docker回滚完成"
}

# 回滚到指定版本
revert_to_version() {
    local version="$1"
    
    if [[ -z "$version" ]]; then
        log_error "请指定版本号 (-v <version>)"
        exit 1
    fi
    
    log_warn "即将回滚到版本: $version"
    
    if [[ "$FORCE" != "true" ]]; then
        read -p "确认回滚到 $version? [y/N] " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            log_info "取消回滚"
            exit 0
        fi
    fi
    
    if [[ "$TARGET" == "k8s" ]]; then
        revert_k8s_version "$version"
    else
        revert_docker_version "$version"
    fi
}

# Kubernetes回滚到指定版本
revert_k8s_version() {
    local version="$1"
    
    log_info "回滚到版本: $version"
    
    # 更新镜像标签
    kubectl set image deployment/backend-deployment \
        backend=formalmath/backend:${version} \
        -n ${NAMESPACE}
    
    kubectl set image deployment/frontend-deployment \
        frontend=formalmath/frontend:${version} \
        -n ${NAMESPACE}
    
    # 等待滚动更新
    kubectl rollout status deployment/backend-deployment -n ${NAMESPACE} --timeout=300s
    kubectl rollout status deployment/frontend-deployment -n ${NAMESPACE} --timeout=300s
    
    # 健康检查
    sleep 10
    if ! health_check; then
        log_error "回滚后健康检查失败"
        exit 1
    fi
    
    log_success "回滚到 $version 完成"
}

# Docker回滚到指定版本
revert_docker_version() {
    local version="$1"
    
    log_info "回滚到版本: $version"
    
    cd "$PROJECT_ROOT/../FormalMath-Enhanced"
    
    # 更新docker-compose文件中的镜像标签
    sed -i "s|formalmath/backend:.*|formalmath/backend:${version}|g" docker-compose.production.yml
    sed -i "s|formalmath/frontend:.*|formalmath/frontend:${version}|g" docker-compose.production.yml
    
    # 拉取指定版本镜像
    docker-compose -f docker-compose.production.yml pull
    
    # 重启服务
    docker-compose -f docker-compose.production.yml up -d
    
    # 等待服务启动
    sleep 30
    
    # 健康检查
    if ! health_check; then
        log_error "回滚后健康检查失败"
        exit 1
    fi
    
    log_success "回滚到 $version 完成"
}

# 健康检查
health_check() {
    log_info "执行健康检查..."
    
    local max_retries=10
    local retry=0
    
    while [[ $retry -lt $max_retries ]]; do
        if curl -sf http://localhost:8000/health > /dev/null 2>&1 && \
           curl -sf http://localhost:80/ > /dev/null 2>&1; then
            log_success "健康检查通过"
            return 0
        fi
        
        retry=$((retry + 1))
        log_info "等待服务启动... ($retry/$max_retries)"
        sleep 10
    done
    
    log_error "健康检查失败"
    return 1
}

# 查看回滚历史
show_history() {
    log_info "查看回滚历史..."
    
    if [[ "$TARGET" == "k8s" ]]; then
        echo "=== 后端部署历史 ==="
        kubectl rollout history deployment/backend-deployment -n ${NAMESPACE}
        echo ""
        echo "=== 前端部署历史 ==="
        kubectl rollout history deployment/frontend-deployment -n ${NAMESPACE}
    else
        echo "=== Docker Compose 历史 ==="
        docker-compose -f "$PROJECT_ROOT/../FormalMath-Enhanced/docker-compose.production.yml" ps
    fi
}

# 主函数
main() {
    local command=""
    local version=""
    TARGET="docker"
    FORCE="false"
    
    # 解析参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            list|rollback|revert|status)
                command="$1"
                shift
                ;;
            -v|--version)
                version="$2"
                shift 2
                ;;
            -n|--namespace)
                NAMESPACE="$2"
                shift 2
                ;;
            -t|--target)
                TARGET="$2"
                shift 2
                ;;
            -f|--force)
                FORCE="true"
                shift
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
        list)
            list_versions
            ;;
        rollback)
            rollback_previous
            ;;
        revert)
            revert_to_version "$version"
            ;;
        status)
            show_history
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
