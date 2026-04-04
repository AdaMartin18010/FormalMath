#!/bin/bash
# ============================================
# FormalMath - 安全加固检查脚本
# 全面的安全检查与加固指南
# ============================================

set -euo pipefail

# 配置
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
REPORT_FILE="${PROJECT_ROOT}/logs/security-report-$(date +%Y%m%d).txt"

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# 计数器
CRITICAL=0
WARNINGS=0
PASSED=0

# 日志函数
log() {
    local level=$1
    shift
    local message="$*"
    local timestamp=$(date '+%Y-%m-%d %H:%M:%S')
    echo "[$timestamp] [$level] $message" | tee -a "$REPORT_FILE"
}

info() { log "INFO" "$@"; }
warn() { log "WARN" "$@"; ((WARNINGS++)); }
critical() { log "CRITICAL" "$@"; ((CRITICAL++)); }
success() { log "PASS" "$@"; ((PASSED++)); }

# 显示帮助
show_help() {
    cat << EOF
FormalMath 安全加固检查脚本

用法: $0 [选项] [命令]

命令:
    full        执行完整安全检查
    docker      Docker安全检查
    nginx       Nginx安全检查
    ssl         SSL/TLS配置检查
    secrets     密钥管理检查
    network     网络安全检查
    file        文件权限检查
    audit       安全审计
    fix         自动修复可修复的问题

选项:
    -o, --output    输出报告文件路径
    -h, --help      显示帮助

示例:
    $0 full
    $0 docker
    $0 ssl
    $0 fix
EOF
}

# 初始化
init() {
    mkdir -p "$(dirname "$REPORT_FILE")"
    info "FormalMath 安全加固检查报告"
    info "检查时间: $(date '+%Y-%m-%d %H:%M:%S')"
    info "========================================"
}

# Docker安全检查
check_docker_security() {
    info "检查 Docker 安全配置..."
    echo "----------------------------------------"
    
    # 检查Docker版本
    local docker_version=$(docker version --format '{{.Server.Version}}' 2>/dev/null || echo "unknown")
    info "Docker版本: $docker_version"
    
    # 检查容器是否以root运行
    info "检查容器用户配置..."
    local root_containers=$(docker ps --format "{{.Names}}" | while read container; do
        if docker inspect --format '{{.Config.User}}' "$container" | grep -q "^$"; then
            echo "$container"
        fi
    done)
    
    if [[ -n "$root_containers" ]]; then
        warn "以下容器以root用户运行:"
        echo "$root_containers" | while read c; do warn "  - $c"; done
    else
        success "所有容器都配置了非root用户"
    fi
    
    # 检查资源限制
    info "检查资源限制配置..."
    docker ps --format "{{.Names}}" | while read container; do
        local memory_limit=$(docker inspect --format '{{.HostConfig.Memory}}' "$container")
        if [[ "$memory_limit" == "0" ]]; then
            warn "容器 $container 未设置内存限制"
        fi
        
        local cpu_limit=$(docker inspect --format '{{.HostConfig.CpuQuota}}' "$container")
        if [[ "$cpu_limit" == "0" ]]; then
            warn "容器 $container 未设置CPU限制"
        fi
    done
    
    # 检查read-only文件系统
    info "检查只读文件系统配置..."
    docker ps --format "{{.Names}}" | while read container; do
        local read_only=$(docker inspect --format '{{.HostConfig.ReadonlyRootfs}}' "$container")
        if [[ "$read_only" != "true" ]]; then
            warn "容器 $container 未启用只读根文件系统"
        fi
    done
    
    # 检查特权模式
    info "检查特权模式..."
    local privileged=$(docker ps --format "{{.Names}}" | while read container; do
        if docker inspect --format '{{.HostConfig.Privileged}}' "$container" | grep -q "true"; then
            echo "$container"
        fi
    done)
    
    if [[ -n "$privileged" ]]; then
        critical "以下容器以特权模式运行:"
        echo "$privileged" | while read c; do critical "  - $c"; done
    else
        success "没有容器以特权模式运行"
    fi
    
    # 检查安全选项
    info "检查安全选项..."
    docker ps --format "{{.Names}}" | while read container; do
        local security_opts=$(docker inspect --format '{{join .HostConfig.SecurityOpts ","}}' "$container")
        if [[ -z "$security_opts" ]]; then
            warn "容器 $container 未配置安全选项"
        fi
    done
    
    # 检查镜像漏洞（如果安装了trivy）
    if command -v trivy &> /dev/null; then
        info "扫描镜像漏洞..."
        docker images --format "{{.Repository}}:{{.Tag}}" | grep "formalmath" | while read image; do
            trivy image --severity HIGH,CRITICAL "$image" 2>/dev/null | tee -a "$REPORT_FILE" || true
        done
    fi
    
    echo ""
}

# Nginx安全检查
check_nginx_security() {
    info "检查 Nginx 安全配置..."
    echo "----------------------------------------"
    
    local nginx_conf="$PROJECT_ROOT/nginx/nginx.conf"
    
    if [[ ! -f "$nginx_conf" ]]; then
        warn "Nginx配置文件不存在: $nginx_conf"
        return
    fi
    
    # 检查Server Tokens
    if grep -q "server_tokens off" "$nginx_conf"; then
        success "已禁用Server Tokens"
    else
        warn "未禁用Server Tokens"
    fi
    
    # 检查X-Frame-Options
    if grep -q "X-Frame-Options" "$nginx_conf"; then
        success "已配置X-Frame-Options"
    else
        warn "未配置X-Frame-Options"
    fi
    
    # 检查X-XSS-Protection
    if grep -q "X-XSS-Protection" "$nginx_conf"; then
        success "已配置X-XSS-Protection"
    else
        warn "未配置X-XSS-Protection"
    fi
    
    # 检查HSTS
    if grep -q "Strict-Transport-Security" "$nginx_conf"; then
        success "已配置HSTS"
    else
        warn "未配置HSTS"
    fi
    
    # 检查SSL配置
    if grep -q "ssl_protocols" "$nginx_conf"; then
        if grep "ssl_protocols" "$nginx_conf" | grep -q "TLSv1.2\|TLSv1.3"; then
            success "使用安全的SSL/TLS协议版本"
        else
            critical "SSL配置使用了不安全的协议版本"
        fi
    fi
    
    # 检查缓冲区大小限制
    if grep -q "client_body_buffer_size\|client_max_body_size" "$nginx_conf"; then
        success "已配置缓冲区大小限制"
    else
        warn "未配置缓冲区大小限制"
    fi
    
    echo ""
}

# SSL/TLS配置检查
check_ssl_configuration() {
    info "检查 SSL/TLS 配置..."
    echo "----------------------------------------"
    
    local ssl_dir="$PROJECT_ROOT/nginx/ssl"
    
    if [[ ! -d "$ssl_dir" ]]; then
        warn "SSL目录不存在: $ssl_dir"
        return
    fi
    
    # 检查证书文件
    if [[ -f "$ssl_dir/formalmath.crt" && -f "$ssl_dir/formalmath.key" ]]; then
        success "SSL证书文件存在"
        
        # 检查证书过期时间
        local expiry=$(openssl x509 -enddate -noout -in "$ssl_dir/formalmath.crt" 2>/dev/null | cut -d= -f2)
        if [[ -n "$expiry" ]]; then
            local expiry_epoch=$(date -d "$expiry" +%s 2>/dev/null || date -j -f "%b %d %H:%M:%S %Y %Z" "$expiry" +%s)
            local now_epoch=$(date +%s)
            local days_until_expiry=$(( (expiry_epoch - now_epoch) / 86400 ))
            
            if [[ $days_until_expiry -lt 7 ]]; then
                critical "SSL证书将在 $days_until_expiry 天后过期"
            elif [[ $days_until_expiry -lt 30 ]]; then
                warn "SSL证书将在 $days_until_expiry 天后过期"
            else
                success "SSL证书有效，剩余 $days_until_expiry 天"
            fi
        fi
        
        # 检查证书密钥匹配
        local cert_modulus=$(openssl x509 -noout -modulus -in "$ssl_dir/formalmath.crt" 2>/dev/null | md5sum | cut -d' ' -f1)
        local key_modulus=$(openssl rsa -noout -modulus -in "$ssl_dir/formalmath.key" 2>/dev/null | md5sum | cut -d' ' -f1)
        
        if [[ "$cert_modulus" == "$key_modulus" ]]; then
            success "证书与密钥匹配"
        else
            critical "证书与密钥不匹配"
        fi
    else
        critical "SSL证书文件缺失"
    fi
    
    # 检查是否为自签名证书
    if openssl x509 -in "$ssl_dir/formalmath.crt" -noout -issuer 2>/dev/null | grep -q "Issuer.*=.*$"; then
        local issuer=$(openssl x509 -in "$ssl_dir/formalmath.crt" -noout -issuer)
        local subject=$(openssl x509 -in "$ssl_dir/formalmath.crt" -noout -subject)
        if [[ "$issuer" == "$subject" ]]; then
            warn "使用自签名证书，生产环境建议使用Let's Encrypt或商业证书"
        fi
    fi
    
    echo ""
}

# 密钥管理检查
check_secrets_management() {
    info "检查密钥管理..."
    echo "----------------------------------------"
    
    # 检查.env文件
    local env_file="$PROJECT_ROOT/.env.production"
    
    if [[ -f "$env_file" ]]; then
        # 检查文件权限
        local perms=$(stat -c "%a" "$env_file" 2>/dev/null || stat -f "%Lp" "$env_file" 2>/dev/null)
        if [[ "$perms" == "600" || "$perms" == "640" ]]; then
            success ".env.production 文件权限正确 ($perms)"
        else
            warn ".env.production 文件权限为 $perms，建议设置为 600"
        fi
        
        # 检查是否使用了默认密钥
        if grep -q "your-secure-secret-key\|change-me\|password123\|admin" "$env_file"; then
            critical "检测到使用默认或弱密钥，请立即更换"
        fi
        
        # 检查密钥长度
        local jwt_secret=$(grep "JWT_SECRET_KEY" "$env_file" | cut -d= -f2)
        if [[ -n "$jwt_secret" && ${#jwt_secret} -lt 32 ]]; then
            warn "JWT_SECRET_KEY 长度过短，建议至少32个字符"
        fi
    else
        warn ".env.production 文件不存在"
    fi
    
    # 检查Git历史
    if [[ -d "$PROJECT_ROOT/.git" ]]; then
        info "检查Git历史中是否包含密钥..."
        local leaked_secrets=$(git -C "$PROJECT_ROOT" log --all --source --remotes --full-history -S "password\|secret\|api_key\|token" --pretty=format:"%h %s" 2>/dev/null | head -10)
        if [[ -n "$leaked_secrets" ]]; then
            warn "Git历史可能包含敏感信息，请检查:"
            echo "$leaked_secrets" | while read line; do warn "  $line"; done
        fi
    fi
    
    echo ""
}

# 网络安全检查
check_network_security() {
    info "检查网络安全..."
    echo "----------------------------------------"
    
    # 检查开放的端口
    info "检查Docker容器开放的端口..."
    docker ps --format "{{.Names}}\t{{.Ports}}" | while read line; do
        info "  $line"
    done
    
    # 检查防火墙状态
    if command -v ufw &> /dev/null; then
        if ufw status | grep -q "Status: active"; then
            success "UFW防火墙已启用"
        else
            warn "UFW防火墙未启用"
        fi
    elif command -v firewall-cmd &> /dev/null; then
        if firewall-cmd --state 2>/dev/null | grep -q "running"; then
            success "firewalld防火墙已启用"
        else
            warn "firewalld防火墙未启用"
        fi
    else
        warn "未检测到防火墙"
    fi
    
    # 检查Fail2ban
    if command -v fail2ban-client &> /dev/null; then
        if fail2ban-client status &>/dev/null; then
            success "Fail2ban已安装并运行"
        else
            warn "Fail2ban已安装但未运行"
        fi
    else
        warn "未安装Fail2ban"
    fi
    
    echo ""
}

# 文件权限检查
check_file_permissions() {
    info "检查文件权限..."
    echo "----------------------------------------"
    
    # 检查敏感文件权限
    local sensitive_files=(
        "$PROJECT_ROOT/.env.production"
        "$PROJECT_ROOT/docker-compose.production.yml"
        "$PROJECT_ROOT/nginx/ssl"
    )
    
    for file in "${sensitive_files[@]}"; do
        if [[ -e "$file" ]]; then
            local perms=$(stat -c "%a" "$file" 2>/dev/null || stat -f "%Lp" "$file" 2>/dev/null)
            local owner=$(stat -c "%U" "$file" 2>/dev/null || stat -f "%Su" "$file" 2>/dev/null)
            
            if [[ -f "$file" ]]; then
                if [[ "$perms" -le 644 ]]; then
                    success "$(basename "$file") 权限正确 ($perms, $owner)"
                else
                    warn "$(basename "$file") 权限过于宽松 ($perms)"
                fi
            elif [[ -d "$file" ]]; then
                if [[ "$perms" -le 755 ]]; then
                    success "$(basename "$file") 目录权限正确 ($perms, $owner)"
                else
                    warn "$(basename "$file") 目录权限过于宽松 ($perms)"
                fi
            fi
        fi
    done
    
    # 检查脚本执行权限
    find "$PROJECT_ROOT/scripts" -name "*.sh" -type f | while read script; do
        if [[ -x "$script" ]]; then
            success "$(basename "$script") 有执行权限"
        else
            warn "$(basename "$script") 缺少执行权限"
        fi
    done
    
    echo ""
}

# 安全审计
check_security_audit() {
    info "执行安全审计..."
    echo "----------------------------------------"
    
    # 检查系统更新
    if command -v apt &> /dev/null; then
        local updates=$(apt list --upgradable 2>/dev/null | grep -c "upgradable" || echo 0)
        if [[ $updates -gt 0 ]]; then
            warn "有 $updates 个软件包可更新"
        else
            success "系统软件包已是最新"
        fi
    fi
    
    # 检查Docker镜像更新
    info "检查Docker镜像更新..."
    docker images --format "{{.Repository}}:{{.Tag}}" | while read image; do
        # 这里可以添加检查远程镜像是否有更新的逻辑
        : # 占位
    done
    
    # 检查日志文件
    info "检查安全相关日志..."
    if [[ -f "/var/log/auth.log" ]]; then
        local failed_logins=$(grep -c "Failed password" /var/log/auth.log 2>/dev/null || echo 0)
        if [[ $failed_logins -gt 10 ]]; then
            warn "检测到 $failed_logins 次登录失败"
        fi
    fi
    
    echo ""
}

# 自动修复
auto_fix() {
    info "尝试自动修复安全问题..."
    echo "----------------------------------------"
    
    # 修复.env文件权限
    if [[ -f "$PROJECT_ROOT/.env.production" ]]; then
        chmod 600 "$PROJECT_ROOT/.env.production"
        success "修复: .env.production 权限设置为 600"
    fi
    
    # 修复SSL目录权限
    if [[ -d "$PROJECT_ROOT/nginx/ssl" ]]; then
        chmod 700 "$PROJECT_ROOT/nginx/ssl"
        find "$PROJECT_ROOT/nginx/ssl" -type f -exec chmod 600 {} \;
        success "修复: SSL目录权限设置完成"
    fi
    
    # 修复脚本执行权限
    find "$PROJECT_ROOT/scripts" -name "*.sh" -type f -exec chmod +x {} \;
    success "修复: 脚本添加执行权限"
    
    # 提示手动修复项
    echo ""
    info "以下问题需要手动修复:"
    echo "  1. 更换默认密钥（JWT_SECRET_KEY, SECRET_KEY等）"
    echo "  2. 配置防火墙规则"
    echo "  3. 启用Fail2ban"
    echo "  4. 更新系统和Docker镜像"
    echo "  5. 配置Nginx安全头"
    echo ""
}

# 生成报告摘要
report_summary() {
    echo ""
    echo "========================================"
    info "安全检查摘要"
    echo "========================================"
    echo ""
    echo -e "${GREEN}通过: $PASSED${NC}"
    echo -e "${YELLOW}警告: $WARNINGS${NC}"
    echo -e "${RED}严重: $CRITICAL${NC}"
    echo ""
    
    if [[ $CRITICAL -gt 0 ]]; then
        critical "发现 $CRITICAL 个严重安全问题，需要立即处理！"
        echo "详细报告: $REPORT_FILE"
        return 1
    elif [[ $WARNINGS -gt 0 ]]; then
        warn "发现 $WARNINGS 个警告，建议尽快处理"
        echo "详细报告: $REPORT_FILE"
        return 0
    else
        success "安全检查通过，未发现安全问题"
        return 0
    fi
}

# 主函数
main() {
    local command=""
    
    # 解析参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            -o|--output)
                REPORT_FILE="$2"
                shift 2
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            full|docker|nginx|ssl|secrets|network|file|audit|fix)
                command=$1
                shift
                ;;
            *)
                echo "未知选项: $1"
                show_help
                exit 1
                ;;
        esac
    done
    
    # 初始化
    init
    
    # 执行检查
    case $command in
        full)
            check_docker_security
            check_nginx_security
            check_ssl_configuration
            check_secrets_management
            check_network_security
            check_file_permissions
            check_security_audit
            report_summary
            ;;
        docker)
            check_docker_security
            ;;
        nginx)
            check_nginx_security
            ;;
        ssl)
            check_ssl_configuration
            ;;
        secrets)
            check_secrets_management
            ;;
        network)
            check_network_security
            ;;
        file)
            check_file_permissions
            ;;
        audit)
            check_security_audit
            ;;
        fix)
            auto_fix
            ;;
        *)
            show_help
            exit 1
            ;;
    esac
}

main "$@"
