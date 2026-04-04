#!/bin/bash

# FormalMath Kubernetes Deployment Script
# 用于部署 FormalMath 应用到 Kubernetes 集群

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 配置
NAMESPACE="formalmath-prod"
DEPLOYMENT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# 打印帮助信息
print_help() {
    echo -e "${BLUE}FormalMath Kubernetes 部署脚本${NC}"
    echo ""
    echo "用法: $0 [命令] [选项]"
    echo ""
    echo "命令:"
    echo "  deploy         部署所有资源"
    echo "  deploy-base    仅部署基础资源（namespace, configmap, secret）"
    echo "  deploy-apps    仅部署应用（deployment, service）"
    echo "  deploy-ingress 部署 ingress"
    echo "  deploy-hpa     部署 HPA 和 PDB"
    echo "  deploy-all     完整部署所有资源"
    echo "  delete         删除所有资源"
    echo "  status         查看部署状态"
    echo "  logs           查看日志"
    echo "  rollback       回滚部署"
    echo "  scale          手动扩缩容"
    echo "  help           显示此帮助信息"
    echo ""
    echo "选项:"
    echo "  --image-tag    指定镜像标签（默认: latest）"
    echo "  --replicas     指定副本数（用于 scale 命令）"
}

# 日志函数
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 检查 kubectl
check_kubectl() {
    if ! command -v kubectl &> /dev/null; then
        log_error "kubectl 未安装或未在 PATH 中"
        exit 1
    fi
    
    if ! kubectl cluster-info &> /dev/null; then
        log_error "无法连接到 Kubernetes 集群"
        exit 1
    fi
    
    log_success "kubectl 已配置"
}

# 检查命名空间
ensure_namespace() {
    if ! kubectl get namespace "$NAMESPACE" &> /dev/null; then
        log_info "创建命名空间: $NAMESPACE"
        kubectl apply -f "$DEPLOYMENT_DIR/01-namespace.yaml"
    fi
}

# 部署基础资源
deploy_base() {
    log_info "部署基础资源..."
    
    ensure_namespace
    
    kubectl apply -f "$DEPLOYMENT_DIR/01-namespace.yaml"
    kubectl apply -f "$DEPLOYMENT_DIR/02-configmap.yaml"
    
    # 检查 Secret 是否存在，如果不存在则创建
    if ! kubectl get secret formalmath-secrets -n "$NAMESPACE" &> /dev/null; then
        log_warn "Secret 不存在，创建示例 Secret"
        kubectl apply -f "$DEPLOYMENT_DIR/03-secret.yaml"
        log_warn "请更新 Secret 中的敏感信息！"
    else
        log_info "Secret 已存在，跳过创建"
    fi
    
    log_success "基础资源部署完成"
}

# 部署应用
deploy_apps() {
    log_info "部署应用..."
    
    # 更新镜像标签（如果指定）
    if [ -n "$IMAGE_TAG" ]; then
        log_info "使用镜像标签: $IMAGE_TAG"
        sed -i.bak "s/:latest/:$IMAGE_TAG/g" "$DEPLOYMENT_DIR/04-backend-deployment.yaml"
        sed -i.bak "s/:latest/:$IMAGE_TAG/g" "$DEPLOYMENT_DIR/05-frontend-deployment.yaml"
    fi
    
    kubectl apply -f "$DEPLOYMENT_DIR/04-backend-deployment.yaml"
    kubectl apply -f "$DEPLOYMENT_DIR/05-frontend-deployment.yaml"
    kubectl apply -f "$DEPLOYMENT_DIR/06-service.yaml"
    
    # 恢复原始文件
    if [ -n "$IMAGE_TAG" ]; then
        mv "$DEPLOYMENT_DIR/04-backend-deployment.yaml.bak" "$DEPLOYMENT_DIR/04-backend-deployment.yaml"
        mv "$DEPLOYMENT_DIR/05-frontend-deployment.yaml.bak" "$DEPLOYMENT_DIR/05-frontend-deployment.yaml"
    fi
    
    log_success "应用部署完成"
    
    # 等待就绪
    log_info "等待 Pod 就绪..."
    kubectl wait --for=condition=available --timeout=300s deployment/backend-deployment -n "$NAMESPACE"
    kubectl wait --for=condition=available --timeout=300s deployment/frontend-deployment -n "$NAMESPACE"
    log_success "所有 Pod 已就绪"
}

# 部署 Ingress
deploy_ingress() {
    log_info "部署 Ingress..."
    
    # 检查 Ingress Controller
    if ! kubectl get pods -n ingress-nginx -l app.kubernetes.io/name=ingress-nginx &> /dev/null; then
        if ! kubectl get pods -n kube-system -l app.kubernetes.io/name=ingress-nginx &> /dev/null; then
            log_warn "未检测到 NGINX Ingress Controller"
            log_warn "请先安装 Ingress Controller:"
            log_warn "  kubectl apply -f https://raw.githubusercontent.com/kubernetes/ingress-nginx/main/deploy/static/provider/cloud/deploy.yaml"
        fi
    fi
    
    kubectl apply -f "$DEPLOYMENT_DIR/07-ingress.yaml"
    log_success "Ingress 部署完成"
}

# 部署 HPA
deploy_hpa() {
    log_info "部署 HPA 和 PDB..."
    
    # 检查 Metrics Server
    if ! kubectl get apiservice v1beta1.metrics.k8s.io &> /dev/null; then
        log_warn "未检测到 Metrics Server，HPA 可能无法正常工作"
        log_warn "请安装 Metrics Server:"
        log_warn "  kubectl apply -f https://github.com/kubernetes-sigs/metrics-server/releases/latest/download/components.yaml"
    fi
    
    kubectl apply -f "$DEPLOYMENT_DIR/08-hpa.yaml"
    log_success "HPA 和 PDB 部署完成"
}

# 完整部署
deploy_all() {
    deploy_base
    deploy_apps
    deploy_ingress
    deploy_hpa
    
    log_success "========================================="
    log_success "FormalMath 完整部署完成！"
    log_success "========================================="
    
    show_status
}

# 删除所有资源
delete_all() {
    log_warn "将删除所有 FormalMath 资源..."
    read -p "确认删除? (y/N): " confirm
    
    if [[ $confirm == [yY] ]]; then
        log_info "删除资源..."
        kubectl delete -f "$DEPLOYMENT_DIR/" --ignore-not-found=true
        log_success "资源删除完成"
    else
        log_info "取消删除"
    fi
}

# 显示状态
show_status() {
    log_info "部署状态:"
    echo ""
    
    echo -e "${BLUE}命名空间:${NC}"
    kubectl get namespace "$NAMESPACE"
    
    echo ""
    echo -e "${BLUE}Deployment:${NC}"
    kubectl get deployments -n "$NAMESPACE"
    
    echo ""
    echo -e "${BLUE}Pods:${NC}"
    kubectl get pods -n "$NAMESPACE"
    
    echo ""
    echo -e "${BLUE}Services:${NC}"
    kubectl get services -n "$NAMESPACE"
    
    echo ""
    echo -e "${BLUE}Ingress:${NC}"
    kubectl get ingress -n "$NAMESPACE"
    
    echo ""
    echo -e "${BLUE}HPA:${NC}"
    kubectl get hpa -n "$NAMESPACE" 2>/dev/null || echo "HPA 未部署"
}

# 查看日志
show_logs() {
    log_info "查看日志..."
    
    echo "选择服务:"
    echo "1) Backend"
    echo "2) Frontend"
    read -p "请输入选项 (1/2): " choice
    
    case $choice in
        1)
            kubectl logs -n "$NAMESPACE" -l app=backend,tier=api --tail=100 -f
            ;;
        2)
            kubectl logs -n "$NAMESPACE" -l app=frontend,tier=web --tail=100 -f
            ;;
        *)
            log_error "无效选项"
            ;;
    esac
}

# 回滚部署
rollback() {
    log_info "回滚部署..."
    
    echo "选择要回滚的服务:"
    echo "1) Backend"
    echo "2) Frontend"
    echo "3) 全部"
    read -p "请输入选项 (1/2/3): " choice
    
    case $choice in
        1)
            kubectl rollout undo deployment/backend-deployment -n "$NAMESPACE"
            ;;
        2)
            kubectl rollout undo deployment/frontend-deployment -n "$NAMESPACE"
            ;;
        3)
            kubectl rollout undo deployment/backend-deployment -n "$NAMESPACE"
            kubectl rollout undo deployment/frontend-deployment -n "$NAMESPACE"
            ;;
        *)
            log_error "无效选项"
            return
            ;;
    esac
    
    log_success "回滚完成"
}

# 手动扩缩容
scale() {
    if [ -z "$REPLICAS" ]; then
        read -p "请输入副本数: " REPLICAS
    fi
    
    if ! [[ "$REPLICAS" =~ ^[0-9]+$ ]]; then
        log_error "副本数必须是数字"
        return
    fi
    
    log_info "扩容到 $REPLICAS 个副本..."
    
    kubectl scale deployment/backend-deployment --replicas="$REPLICAS" -n "$NAMESPACE"
    kubectl scale deployment/frontend-deployment --replicas="$REPLICAS" -n "$NAMESPACE"
    
    log_success "扩缩容完成"
}

# 主函数
main() {
    # 解析参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            --image-tag)
                IMAGE_TAG="$2"
                shift 2
                ;;
            --replicas)
                REPLICAS="$2"
                shift 2
                ;;
            -*)
                log_error "未知选项: $1"
                exit 1
                ;;
            *)
                COMMAND="$1"
                shift
                ;;
        esac
    done
    
    # 执行命令
    case $COMMAND in
        deploy)
            check_kubectl
            deploy_apps
            ;;
        deploy-base)
            check_kubectl
            deploy_base
            ;;
        deploy-apps)
            check_kubectl
            deploy_apps
            ;;
        deploy-ingress)
            check_kubectl
            deploy_ingress
            ;;
        deploy-hpa)
            check_kubectl
            deploy_hpa
            ;;
        deploy-all)
            check_kubectl
            deploy_all
            ;;
        delete)
            check_kubectl
            delete_all
            ;;
        status)
            check_kubectl
            show_status
            ;;
        logs)
            check_kubectl
            show_logs
            ;;
        rollback)
            check_kubectl
            rollback
            ;;
        scale)
            check_kubectl
            scale
            ;;
        help|--help|-h|"")
            print_help
            ;;
        *)
            log_error "未知命令: $COMMAND"
            print_help
            exit 1
            ;;
    esac
}

main "$@"
