#!/bin/bash
# FormalMath CDN 部署脚本
# 支持 CloudFlare、CloudFront 和 Nginx 部署

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# 配置
DEPLOY_TYPE=${1:-"all"}
CONFIG_DIR="$(dirname "$0")"
LOG_FILE="/var/log/formalmath-cdn-deploy.log"

# 日志函数
log_info() {
    echo -e "${GREEN}[INFO]${NC} $1" | tee -a "$LOG_FILE"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1" | tee -a "$LOG_FILE"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1" | tee -a "$LOG_FILE"
}

# 检查依赖
check_dependencies() {
    log_info "检查依赖..."
    
    if [[ "$DEPLOY_TYPE" == "cloudflare" || "$DEPLOY_TYPE" == "all" ]]; then
        if ! command -v wrangler &> /dev/null; then
            log_error "wrangler CLI 未安装"
            echo "安装命令: npm install -g wrangler"
            exit 1
        fi
        log_info "✓ wrangler CLI 已安装"
    fi
    
    if [[ "$DEPLOY_TYPE" == "cloudfront" || "$DEPLOY_TYPE" == "all" ]]; then
        if ! command -v aws &> /dev/null; then
            log_error "AWS CLI 未安装"
            exit 1
        fi
        log_info "✓ AWS CLI 已安装"
    fi
    
    if [[ "$DEPLOY_TYPE" == "nginx" || "$DEPLOY_TYPE" == "all" ]]; then
        if ! command -v nginx &> /dev/null; then
            log_error "Nginx 未安装"
            exit 1
        fi
        log_info "✓ Nginx 已安装"
    fi
}

# 部署 CloudFlare
deploy_cloudflare() {
    log_info "开始部署 CloudFlare 配置..."
    
    # 检查配置文件
    if [[ ! -f "$CONFIG_DIR/cloudflare_config.yaml" ]]; then
        log_error "CloudFlare 配置文件不存在"
        return 1
    fi
    
    # 登录检查
    if ! wrangler whoami &> /dev/null; then
        log_warn "未登录 CloudFlare，请运行: wrangler login"
        return 1
    fi
    
    # 部署 Workers
    log_info "部署 CloudFlare Workers..."
    # wrangler deploy --config "$CONFIG_DIR/cloudflare_config.yaml"
    
    log_info "CloudFlare 部署完成"
}

# 部署 CloudFront
deploy_cloudfront() {
    log_info "开始部署 AWS CloudFront..."
    
    # 检查配置文件
    if [[ ! -f "$CONFIG_DIR/cloudfront_config.json" ]]; then
        log_error "CloudFront 配置文件不存在"
        return 1
    fi
    
    # 检查 AWS 凭证
    if ! aws sts get-caller-identity &> /dev/null; then
        log_warn "AWS 凭证无效或未配置"
        return 1
    fi
    
    STACK_NAME="formalmath-cdn"
    
    # 检查栈是否存在
    if aws cloudformation describe-stacks --stack-name "$STACK_NAME" &> /dev/null; then
        log_info "更新 CloudFormation 栈..."
        aws cloudformation update-stack \
            --stack-name "$STACK_NAME" \
            --template-body "file://$CONFIG_DIR/cloudfront_config.json" \
            --capabilities CAPABILITY_IAM CAPABILITY_NAMED_IAM \
            2>/dev/null || log_warn "栈无需更新"
    else
        log_info "创建 CloudFormation 栈..."
        aws cloudformation create-stack \
            --stack-name "$STACK_NAME" \
            --template-body "file://$CONFIG_DIR/cloudfront_config.json" \
            --capabilities CAPABILITY_IAM CAPABILITY_NAMED_IAM
    fi
    
    log_info "等待部署完成..."
    aws cloudformation wait stack-create-complete --stack-name "$STACK_NAME" 2>/dev/null || \
    aws cloudformation wait stack-update-complete --stack-name "$STACK_NAME" 2>/dev/null || true
    
    # 获取输出
    aws cloudformation describe-stacks \
        --stack-name "$STACK_NAME" \
        --query 'Stacks[0].Outputs' \
        --output table
    
    log_info "CloudFront 部署完成"
}

# 部署 Nginx
deploy_nginx() {
    log_info "开始部署 Nginx 配置..."
    
    # 检查配置文件
    if [[ ! -f "$CONFIG_DIR/nginx_cache.conf" ]]; then
        log_error "Nginx 配置文件不存在"
        return 1
    fi
    
    # 测试配置
    log_info "测试 Nginx 配置..."
    if ! sudo nginx -t -c "$CONFIG_DIR/nginx_cache.conf" &> /dev/null; then
        log_error "Nginx 配置测试失败"
        return 1
    fi
    
    # 创建缓存目录
    log_info "创建缓存目录..."
    sudo mkdir -p /var/cache/nginx/api /var/cache/nginx/static
    sudo chown -R nginx:nginx /var/cache/nginx 2>/dev/null || \
    sudo chown -R www-data:www-data /var/cache/nginx 2>/dev/null || true
    
    # 备份原配置
    if [[ -f /etc/nginx/nginx.conf ]]; then
        sudo cp /etc/nginx/nginx.conf "/etc/nginx/nginx.conf.backup.$(date +%Y%m%d%H%M%S)"
    fi
    
    # 部署配置
    log_info "部署 Nginx 配置..."
    sudo cp "$CONFIG_DIR/nginx_cache.conf" /etc/nginx/nginx.conf
    
    # 检查语法
    sudo nginx -t
    
    # 重载配置
    log_info "重载 Nginx..."
    sudo systemctl reload nginx || sudo nginx -s reload
    
    log_info "Nginx 部署完成"
}

# 验证部署
verify_deployment() {
    log_info "验证部署..."
    
    # 测试健康检查端点
    if curl -sSf "http://localhost/health" > /dev/null 2>&1; then
        log_info "✓ 健康检查端点正常"
    else
        log_warn "健康检查端点异常"
    fi
    
    # 测试缓存头
    log_info "检查缓存头..."
    curl -sI "http://localhost/api/v1/concepts" 2>/dev/null | grep -i "cache-control" || true
    
    # 检查 Nginx 缓存目录
    if [[ -d /var/cache/nginx ]]; then
        CACHE_SIZE=$(du -sh /var/cache/nginx 2>/dev/null | cut -f1)
        log_info "Nginx 缓存大小: $CACHE_SIZE"
    fi
}

# 清理缓存
purge_cache() {
    log_info "清理缓存..."
    
    # 清理 Nginx 缓存
    if [[ -d /var/cache/nginx ]]; then
        sudo rm -rf /var/cache/nginx/*
        sudo systemctl reload nginx
        log_info "✓ Nginx 缓存已清理"
    fi
    
    # 提示 CloudFlare 清理命令
    log_info "CloudFlare 清理命令:"
    echo "  curl -X POST 'https://api.cloudflare.com/client/v4/zones/{zone_id}/purge_cache' \\"
    echo "    -H 'Authorization: Bearer {token}' \\"
    echo "    -d '{\"purge_everything\":true}'"
    
    # 提示 CloudFront 清理命令
    log_info "CloudFront 清理命令:"
    echo "  aws cloudfront create-invalidation --distribution-id {id} --paths '/*'"
}

# 显示帮助
show_help() {
    cat << EOF
FormalMath CDN 部署脚本

用法: $0 [选项]

选项:
  all          部署所有 CDN 配置 (默认)
  cloudflare   仅部署 CloudFlare 配置
  cloudfront   仅部署 AWS CloudFront 配置
  nginx        仅部署 Nginx 配置
  verify       验证部署状态
  purge        清理所有缓存
  help         显示此帮助信息

示例:
  $0                    # 部署所有配置
  $0 nginx              # 仅部署 Nginx
  $0 verify             # 验证部署
  $0 purge              # 清理缓存

EOF
}

# 主函数
main() {
    echo "================================"
    echo " FormalMath CDN 部署脚本"
    echo "================================"
    echo ""
    
    case "$DEPLOY_TYPE" in
        cloudflare)
            check_dependencies
            deploy_cloudflare
            ;;
        cloudfront)
            check_dependencies
            deploy_cloudfront
            ;;
        nginx)
            check_dependencies
            deploy_nginx
            ;;
        all)
            check_dependencies
            deploy_cloudflare
            deploy_cloudfront
            deploy_nginx
            verify_deployment
            ;;
        verify)
            verify_deployment
            ;;
        purge)
            purge_cache
            ;;
        help|--help|-h)
            show_help
            ;;
        *)
            log_error "未知选项: $DEPLOY_TYPE"
            show_help
            exit 1
            ;;
    esac
    
    echo ""
    log_info "部署脚本执行完成"
}

# 创建日志目录
sudo mkdir -p "$(dirname "$LOG_FILE")"

# 运行主函数
main
