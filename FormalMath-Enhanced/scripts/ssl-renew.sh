#!/bin/bash
# ============================================
# FormalMath - SSL证书自动续期脚本
# 支持Let's Encrypt自动申请和续期
# ============================================

set -euo pipefail

# 配置
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
CERT_DIR="${PROJECT_ROOT}/nginx/ssl"
WEBROOT_DIR="${PROJECT_ROOT}/certbot-webroot"
LOG_FILE="${PROJECT_ROOT}/logs/ssl-renew.log"
CONFIG_FILE="${PROJECT_ROOT}/config/ssl.conf"

# 默认配置
DOMAINS=""
EMAIL="admin@example.com"
STAGING=false
FORCE_RENEW=false

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
FormalMath SSL证书管理脚本

用法: $0 [选项] [命令]

命令:
    init        初始化证书（首次申请）
    renew       续期证书
    check       检查证书状态
    revoke      吊销证书
    cleanup     清理过期证书

选项:
    -d, --domains       域名列表，逗号分隔 (例如: example.com,www.example.com)
    -e, --email         管理员邮箱
    -s, --staging       使用Let's Encrypt测试环境
    -f, --force         强制续期
    -h, --help          显示帮助

示例:
    $0 init -d formalmath.example.com,www.formalmath.example.com -e admin@example.com
    $0 renew
    $0 check
EOF
}

# 加载配置文件
load_config() {
    if [[ -f "$CONFIG_FILE" ]]; then
        info "加载配置文件: $CONFIG_FILE"
        source "$CONFIG_FILE"
    fi
}

# 检查依赖
check_dependencies() {
    info "检查依赖..."
    
    if ! command -v docker &> /dev/null; then
        error "Docker 未安装"
        exit 1
    fi
    
    if ! command -v certbot &> /dev/null; then
        info "使用Docker运行Certbot"
        USE_DOCKER_CERTBOT=true
    else
        USE_DOCKER_CERTBOT=false
    fi
}

# 创建必要的目录
setup_directories() {
    info "创建必要的目录..."
    mkdir -p "$CERT_DIR" "$WEBROOT_DIR" "$(dirname "$LOG_FILE")"
    chmod 755 "$CERT_DIR" "$WEBROOT_DIR"
}

# 初始化证书（首次申请）
init_certificate() {
    info "初始化SSL证书..."
    
    if [[ -z "$DOMAINS" ]]; then
        error "请指定域名 (-d domain1.com,domain2.com)"
        exit 1
    fi
    
    # 转换为Certbot参数格式
    local domain_args=""
    IFS=',' read -ra DOMAIN_ARRAY <<< "$DOMAINS"
    for domain in "${DOMAIN_ARRAY[@]}"; do
        domain_args="$domain_args -d $domain"
    done
    
    local staging_arg=""
    if [[ "$STAGING" == true ]]; then
        staging_arg="--staging"
        warn "使用测试环境，生成的证书不受浏览器信任"
    fi
    
    info "申请域名: $DOMAINS"
    
    if [[ "$USE_DOCKER_CERTBOT" == true ]]; then
        docker run -it --rm \
            -v "$CERT_DIR:/etc/letsencrypt" \
            -v "$WEBROOT_DIR:/data/letsencrypt" \
            certbot/certbot certonly \
            $staging_arg \
            --webroot \
            --webroot-path /data/letsencrypt \
            $domain_args \
            --agree-tos \
            --non-interactive \
            --email "$EMAIL" \
            --deploy-hook "docker exec formalmath-nginx nginx -s reload || true"
    else
        certbot certonly \
            $staging_arg \
            --webroot \
            --webroot-path "$WEBROOT_DIR" \
            $domain_args \
            --agree-tos \
            --non-interactive \
            --email "$EMAIL" \
            --deploy-hook "docker exec formalmath-nginx nginx -s reload || true"
    fi
    
    if [[ $? -eq 0 ]]; then
        success "证书申请成功"
        # 创建符号链接方便使用
        setup_certificate_links
    else
        error "证书申请失败"
        exit 1
    fi
}

# 设置证书链接
setup_certificate_links() {
    info "设置证书链接..."
    
    local primary_domain="${DOMAIN_ARRAY[0]}"
    local cert_path="/etc/letsencrypt/live/$primary_domain"
    
    # 创建通用命名的符号链接
    ln -sf "$cert_path/fullchain.pem" "$CERT_DIR/formalmath.crt" || true
    ln -sf "$cert_path/privkey.pem" "$CERT_DIR/formalmath.key" || true
    ln -sf "$cert_path/chain.pem" "$CERT_DIR/chain.crt" || true
    
    success "证书链接已创建"
}

# 续期证书
renew_certificates() {
    info "检查并续期证书..."
    
    local force_arg=""
    if [[ "$FORCE_RENEW" == true ]]; then
        force_arg="--force-renew"
    fi
    
    if [[ "$USE_DOCKER_CERTBOT" == true ]]; then
        docker run -it --rm \
            -v "$CERT_DIR:/etc/letsencrypt" \
            -v "$WEBROOT_DIR:/data/letsencrypt" \
            certbot/certbot renew \
            $force_arg \
            --webroot-path /data/letsencrypt \
            --quiet \
            --deploy-hook "docker exec formalmath-nginx nginx -s reload || true"
    else
        certbot renew \
            $force_arg \
            --webroot-path "$WEBROOT_DIR" \
            --quiet \
            --deploy-hook "docker exec formalmath-nginx nginx -s reload || true"
    fi
    
    local exit_code=$?
    if [[ $exit_code -eq 0 ]]; then
        success "证书续期检查完成"
    else
        error "证书续期失败 (退出码: $exit_code)"
        return $exit_code
    fi
}

# 检查证书状态
check_status() {
    info "检查证书状态..."
    
    if [[ "$USE_DOCKER_CERTBOT" == true ]]; then
        docker run -it --rm \
            -v "$CERT_DIR:/etc/letsencrypt" \
            certbot/certbot certificates
    else
        certbot certificates
    fi
    
    # 额外检查证书过期时间
    for cert in "$CERT_DIR"/*/fullchain.pem; do
        if [[ -f "$cert" ]]; then
            local domain=$(basename "$(dirname "$cert")")
            local expiry=$(openssl x509 -enddate -noout -in "$cert" | cut -d= -f2)
            local expiry_epoch=$(date -d "$expiry" +%s 2>/dev/null || date -j -f "%b %d %H:%M:%S %Y %Z" "$expiry" +%s)
            local now_epoch=$(date +%s)
            local days_until_expiry=$(( (expiry_epoch - now_epoch) / 86400 ))
            
            info "域名: $domain"
            info "  过期时间: $expiry"
            info "  剩余天数: $days_until_expiry"
            
            if [[ $days_until_expiry -lt 7 ]]; then
                warn "  警告：证书即将过期！"
            fi
        fi
    done
}

# 吊销证书
revoke_certificate() {
    warn "即将吊销证书..."
    read -p "确定要继续吗? (yes/no) " confirm
    
    if [[ "$confirm" != "yes" ]]; then
        info "操作已取消"
        return 0
    fi
    
    if [[ -z "$DOMAINS" ]]; then
        error "请指定要吊销的域名"
        exit 1
    fi
    
    local domain="${DOMAIN_ARRAY[0]}"
    
    if [[ "$USE_DOCKER_CERTBOT" == true ]]; then
        docker run -it --rm \
            -v "$CERT_DIR:/etc/letsencrypt" \
            certbot/certbot revoke \
            --cert-name "$domain" \
            --reason cessationofoperation
    else
        certbot revoke \
            --cert-name "$domain" \
            --reason cessationofoperation
    fi
    
    if [[ $? -eq 0 ]]; then
        success "证书已吊销"
    else
        error "吊销失败"
        exit 1
    fi
}

# 清理过期证书
cleanup_certificates() {
    info "清理过期证书..."
    
    if [[ "$USE_DOCKER_CERTBOT" == true ]]; then
        docker run -it --rm \
            -v "$CERT_DIR:/etc/letsencrypt" \
            certbot/certbot delete --non-interactive 2>/dev/null || true
    else
        certbot delete --non-interactive 2>/dev/null || true
    fi
    
    success "清理完成"
}

# 设置自动续期定时任务
setup_cron() {
    info "设置自动续期定时任务..."
    
    local cron_job="0 3 * * * $SCRIPT_DIR/ssl-renew.sh renew >> $LOG_FILE 2>&1"
    
    # 检查是否已存在
    if crontab -l 2>/dev/null | grep -q "$SCRIPT_DIR/ssl-renew.sh"; then
        info "定时任务已存在"
    else
        (crontab -l 2>/dev/null; echo "$cron_job") | crontab -
        success "定时任务已添加: 每天凌晨3点检查续期"
    fi
}

# 主函数
main() {
    local command=""
    
    # 解析参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            -d|--domains)
                DOMAINS="$2"
                shift 2
                ;;
            -e|--email)
                EMAIL="$2"
                shift 2
                ;;
            -s|--staging)
                STAGING=true
                shift
                ;;
            -f|--force)
                FORCE_RENEW=true
                shift
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            init|renew|check|revoke|cleanup)
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
    
    # 执行命令
    case $command in
        init)
            check_dependencies
            setup_directories
            init_certificate
            setup_cron
            ;;
        renew)
            check_dependencies
            setup_directories
            renew_certificates
            ;;
        check)
            check_dependencies
            check_status
            ;;
        revoke)
            check_dependencies
            revoke_certificate
            ;;
        cleanup)
            check_dependencies
            cleanup_certificates
            ;;
        *)
            show_help
            exit 1
            ;;
    esac
}

# 确保日志目录存在
mkdir -p "$(dirname "$0")/../logs"

main "$@"
