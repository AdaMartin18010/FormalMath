#!/bin/bash
# ============================================
# FormalMath - 部署前检查脚本
# 验证所有配置是否正确
# ============================================

set -euo pipefail

# 配置
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# 计数器
CHECKS_PASSED=0
CHECKS_FAILED=0
CHECKS_WARNING=0

# 输出函数
print_header() {
    echo ""
    echo "========================================"
    echo "$1"
    echo "========================================"
}

print_pass() {
    echo -e "${GREEN}✓${NC} $1"
    ((CHECKS_PASSED++))
}

print_fail() {
    echo -e "${RED}✗${NC} $1"
    ((CHECKS_FAILED++))
}

print_warn() {
    echo -e "${YELLOW}⚠${NC} $1"
    ((CHECKS_WARNING++))
}

# 检查Docker
check_docker() {
    print_header "检查 Docker 环境"
    
    if command -v docker &> /dev/null; then
        print_pass "Docker 已安装"
        local version=$(docker version --format '{{.Server.Version}}' 2>/dev/null || echo "unknown")
        echo "  版本: $version"
    else
        print_fail "Docker 未安装"
    fi
    
    if command -v docker-compose &> /dev/null; then
        print_pass "Docker Compose 已安装"
    else
        print_fail "Docker Compose 未安装"
    fi
    
    if docker info &> /dev/null; then
        print_pass "Docker 服务运行正常"
    else
        print_fail "Docker 服务未运行或当前用户无权限"
    fi
}

# 检查配置文件
check_config_files() {
    print_header "检查配置文件"
    
    # 检查生产环境变量文件
    if [[ -f "$PROJECT_ROOT/.env.production" ]]; then
        print_pass ".env.production 文件存在"
        
        # 检查关键配置
        if grep -q "SECRET_KEY" "$PROJECT_ROOT/.env.production"; then
            local secret=$(grep "SECRET_KEY" "$PROJECT_ROOT/.env.production" | cut -d= -f2)
            if [[ ${#secret} -lt 20 || "$secret" == *"your-secure-secret-key"* ]]; then
                print_fail "SECRET_KEY 使用了默认值或长度不足"
            else
                print_pass "SECRET_KEY 已配置"
            fi
        else
            print_fail ".env.production 缺少 SECRET_KEY"
        fi
        
        if grep -q "DEBUG=false" "$PROJECT_ROOT/.env.production"; then
            print_pass "DEBUG 已设置为 false"
        else
            print_warn "DEBUG 未设置为 false"
        fi
    else
        print_fail ".env.production 文件不存在"
    fi
    
    # 检查Docker Compose配置
    if [[ -f "$PROJECT_ROOT/docker-compose.production.yml" ]]; then
        print_pass "docker-compose.production.yml 文件存在"
    else
        print_fail "docker-compose.production.yml 文件不存在"
    fi
    
    # 检查Dockerfile
    if [[ -f "$PROJECT_ROOT/Dockerfile.backend.optimized" ]]; then
        print_pass "Dockerfile.backend.optimized 文件存在"
    else
        print_fail "Dockerfile.backend.optimized 文件不存在"
    fi
    
    if [[ -f "$PROJECT_ROOT/Dockerfile.frontend.optimized" ]]; then
        print_pass "Dockerfile.frontend.optimized 文件存在"
    else
        print_fail "Dockerfile.frontend.optimized 文件不存在"
    fi
}

# 检查SSL配置
check_ssl() {
    print_header "检查 SSL/TLS 配置"
    
    local ssl_dir="$PROJECT_ROOT/nginx/ssl"
    
    if [[ -d "$ssl_dir" ]]; then
        print_pass "SSL 目录存在"
        
        if [[ -f "$ssl_dir/formalmath.crt" ]]; then
            print_pass "SSL 证书文件存在"
            
            # 检查证书过期时间
            if command -v openssl &> /dev/null; then
                local expiry=$(openssl x509 -enddate -noout -in "$ssl_dir/formalmath.crt" 2>/dev/null | cut -d= -f2)
                if [[ -n "$expiry" ]]; then
                    local expiry_epoch=$(date -d "$expiry" +%s 2>/dev/null || date -j -f "%b %d %H:%M:%S %Y %Z" "$expiry" +%s)
                    local now_epoch=$(date +%s)
                    local days_until_expiry=$(( (expiry_epoch - now_epoch) / 86400 ))
                    
                    if [[ $days_until_expiry -gt 30 ]]; then
                        print_pass "SSL 证书有效 (剩余 $days_until_expiry 天)"
                    elif [[ $days_until_expiry -gt 7 ]]; then
                        print_warn "SSL 证书即将过期 (剩余 $days_until_expiry 天)"
                    else
                        print_fail "SSL 证书即将过期 (剩余 $days_until_expiry 天)"
                    fi
                fi
            fi
        else
            print_warn "SSL 证书文件不存在，将使用HTTP或自动生成证书"
        fi
        
        if [[ -f "$ssl_dir/formalmath.key" ]]; then
            print_pass "SSL 私钥文件存在"
            
            # 检查密钥权限
            local perms=$(stat -c "%a" "$ssl_dir/formalmath.key" 2>/dev/null || stat -f "%Lp" "$ssl_dir/formalmath.key" 2>/dev/null)
            if [[ "$perms" == "600" ]]; then
                print_pass "SSL 私钥文件权限正确 (600)"
            else
                print_warn "SSL 私钥文件权限为 $perms，建议设置为 600"
            fi
        fi
    else
        print_warn "SSL 目录不存在"
    fi
}

# 检查目录结构
check_directories() {
    print_header "检查目录结构"
    
    local dirs=("logs" "backups" "data" "nginx/conf.d" "nginx/ssl")
    
    for dir in "${dirs[@]}"; do
        if [[ -d "$PROJECT_ROOT/$dir" ]]; then
            print_pass "目录存在: $dir"
        else
            print_warn "目录不存在: $dir (将自动创建)"
            mkdir -p "$PROJECT_ROOT/$dir"
        fi
    done
}

# 检查脚本权限
check_scripts() {
    print_header "检查脚本权限"
    
    local scripts=("deploy.sh" "health-check.sh" "ssl-renew.sh" "database-migrate.sh" "log-rotate.sh" "backup-scheduler.sh" "security-hardening.sh")
    
    for script in "${scripts[@]}"; do
        local script_path="$PROJECT_ROOT/scripts/$script"
        if [[ -f "$script_path" ]]; then
            if [[ -x "$script_path" ]]; then
                print_pass "脚本可执行: $script"
            else
                print_warn "脚本缺少执行权限: $script"
                chmod +x "$script_path"
            fi
        else
            print_fail "脚本不存在: $script"
        fi
    done
}

# 检查系统资源
check_system_resources() {
    print_header "检查系统资源"
    
    # 检查磁盘空间
    local disk_usage=$(df -h "$PROJECT_ROOT" | awk 'NR==2 {print $5}' | sed 's/%//')
    if [[ $disk_usage -lt 80 ]]; then
        print_pass "磁盘空间充足 (${disk_usage}% 使用)"
    elif [[ $disk_usage -lt 90 ]]; then
        print_warn "磁盘空间不足 (${disk_usage}% 使用)"
    else
        print_fail "磁盘空间严重不足 (${disk_usage}% 使用)"
    fi
    
    # 检查内存
    if command -v free &> /dev/null; then
        local mem_usage=$(free | grep Mem | awk '{printf "%.0f", $3/$2 * 100.0}')
        if [[ $mem_usage -lt 80 ]]; then
            print_pass "内存充足 (${mem_usage}% 使用)"
        else
            print_warn "内存使用率较高 (${mem_usage}% 使用)"
        fi
    fi
    
    # 检查端口占用
    local ports=(80 443 8000 6379)
    for port in "${ports[@]}"; do
        if netstat -tuln 2>/dev/null | grep -q ":$port " || ss -tuln 2>/dev/null | grep -q ":$port "; then
            print_warn "端口 $port 已被占用"
        else
            print_pass "端口 $port 可用"
        fi
    done
}

# 检查网络配置
check_network() {
    print_header "检查网络配置"
    
    # 检查主机名
    local hostname=$(hostname)
    echo "  主机名: $hostname"
    
    # 检查IP地址
    local ip=$(hostname -I 2>/dev/null | awk '{print $1}' || echo "unknown")
    echo "  IP地址: $ip"
    
    # 检查互联网连接
    if ping -c 1 8.8.8.8 &> /dev/null || ping -c 1 google.com &> /dev/null; then
        print_pass "网络连接正常"
    else
        print_warn "网络连接异常"
    fi
}

# 检查定时任务
check_cron() {
    print_header "检查定时任务配置"
    
    if command -v crontab &> /dev/null; then
        local cron_jobs=$(crontab -l 2>/dev/null | grep -c "formalmath" || echo 0)
        if [[ $cron_jobs -gt 0 ]]; then
            print_pass "已配置 $cron_jobs 个定时任务"
        else
            print_warn "未配置定时任务，建议配置自动备份和SSL续期"
        fi
    else
        print_warn "crontab 未安装"
    fi
}

# 显示检查结果
show_summary() {
    echo ""
    echo "========================================"
    echo "检查完成"
    echo "========================================"
    echo ""
    echo -e "${GREEN}通过: $CHECKS_PASSED${NC}"
    echo -e "${YELLOW}警告: $CHECKS_WARNING${NC}"
    echo -e "${RED}失败: $CHECKS_FAILED${NC}"
    echo ""
    
    if [[ $CHECKS_FAILED -gt 0 ]]; then
        echo -e "${RED}检查未通过，请修复上述问题后再部署${NC}"
        exit 1
    elif [[ $CHECKS_WARNING -gt 0 ]]; then
        echo -e "${YELLOW}检查通过，但有 $CHECKS_WARNING 个警告，建议处理${NC}"
        echo ""
        read -p "是否继续部署? (y/N) " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            exit 1
        fi
    else
        echo -e "${GREEN}所有检查通过，可以进行部署${NC}"
    fi
}

# 主函数
main() {
    echo "FormalMath 部署前检查"
    echo "======================"
    echo ""
    
    check_docker
    check_config_files
    check_ssl
    check_directories
    check_scripts
    check_system_resources
    check_network
    check_cron
    
    show_summary
}

main "$@"
