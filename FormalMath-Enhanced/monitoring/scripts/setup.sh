#!/bin/bash
# FormalMath-Enhanced 监控系统安装脚本
# 适用于 Ubuntu/Debian/CentOS

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# 日志函数
log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 检测操作系统
detect_os() {
    if [[ -f /etc/os-release ]]; then
        . /etc/os-release
        OS=$NAME
        VERSION=$VERSION_ID
    else
        log_error "无法检测操作系统"
        exit 1
    fi
    log_info "检测到操作系统: $OS $VERSION"
}

# 安装 Docker
install_docker() {
    log_info "检查 Docker..."
    
    if command -v docker &> /dev/null; then
        log_warn "Docker 已安装，跳过"
        docker --version
        return
    fi
    
    log_info "安装 Docker..."
    
    if [[ "$OS" == *"Ubuntu"* ]] || [[ "$OS" == *"Debian"* ]]; then
        apt-get update
        apt-get install -y apt-transport-https ca-certificates curl gnupg lsb-release
        curl -fsSL https://download.docker.com/linux/$(echo $OS | tr '[:upper:]' '[:lower:]')/gpg | gpg --dearmor -o /usr/share/keyrings/docker-archive-keyring.gpg
        echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/docker-archive-keyring.gpg] https://download.docker.com/linux/$(echo $OS | tr '[:upper:]' '[:lower:]') $(lsb_release -cs) stable" | tee /etc/apt/sources.list.d/docker.list > /dev/null
        apt-get update
        apt-get install -y docker-ce docker-ce-cli containerd.io docker-compose-plugin
    elif [[ "$OS" == *"CentOS"* ]] || [[ "$OS" == *"Red Hat"* ]]; then
        yum install -y yum-utils
        yum-config-manager --add-repo https://download.docker.com/linux/centos/docker-ce.repo
        yum install -y docker-ce docker-ce-cli containerd.io docker-compose-plugin
        systemctl start docker
        systemctl enable docker
    fi
    
    log_info "Docker 安装完成"
    docker --version
}

# 安装 Docker Compose
install_docker_compose() {
    log_info "检查 Docker Compose..."
    
    if command -v docker-compose &> /dev/null; then
        log_warn "Docker Compose 已安装，跳过"
        docker-compose --version
        return
    fi
    
    log_info "安装 Docker Compose..."
    
    DOCKER_COMPOSE_VERSION=v2.22.0
    curl -L "https://github.com/docker/compose/releases/download/${DOCKER_COMPOSE_VERSION}/docker-compose-$(uname -s)-$(uname -m)" -o /usr/local/bin/docker-compose
    chmod +x /usr/local/bin/docker-compose
    ln -sf /usr/local/bin/docker-compose /usr/bin/docker-compose
    
    log_info "Docker Compose 安装完成"
    docker-compose --version
}

# 配置系统参数
configure_system() {
    log_info "配置系统参数..."
    
    # 配置 Elasticsearch 内存参数
    if ! grep -q "vm.max_map_count=262144" /etc/sysctl.conf; then
        echo "vm.max_map_count=262144" >> /etc/sysctl.conf
    fi
    sysctl -w vm.max_map_count=262144
    
    log_info "系统参数配置完成"
}

# 创建日志目录
create_directories() {
    log_info "创建日志目录..."
    
    mkdir -p /var/log/formalmath/api
    mkdir -p /var/log/formalmath/adaptive-learning
    mkdir -p /var/log/formalmath/cognitive-diagnosis
    mkdir -p /var/log/formalmath/evaluation-system
    mkdir -p /var/log/formalmath/lean4
    mkdir -p /var/log/formalmath/ai-formalization
    mkdir -p /var/log/formalmath/knowledge-graph
    
    chmod -R 755 /var/log/formalmath
    
    log_info "日志目录创建完成"
}

# 配置环境变量
setup_environment() {
    log_info "配置环境变量..."
    
    if [[ ! -f .env ]]; then
        cp .env.example .env
        log_warn "请编辑 .env 文件配置必要的环境变量"
    fi
}

# 启动服务
start_services() {
    log_info "启动监控服务..."
    
    docker-compose up -d
    
    log_info "等待服务初始化..."
    sleep 30
    
    # 检查服务状态
    if docker-compose ps | grep -q "Up"; then
        log_info "服务启动成功"
    else
        log_error "部分服务启动失败，请检查日志"
        docker-compose logs
        exit 1
    fi
}

# 显示访问信息
show_access_info() {
    log_info "=== FormalMath 监控系统已就绪 ==="
    echo ""
    echo "访问地址:"
    echo "  Grafana:      http://localhost:3000"
    echo "  Prometheus:   http://localhost:9090"
    echo "  Alertmanager: http://localhost:9093"
    echo "  Kibana:       http://localhost:5601"
    echo ""
}

# 主函数
main() {
    echo "=========================================="
    echo "FormalMath-Enhanced 监控系统安装程序"
    echo "=========================================="
    echo ""
    
    detect_os
    install_docker
    install_docker_compose
    configure_system
    create_directories
    setup_environment
    start_services
    show_access_info
    
    log_info "安装完成!"
}

# 运行主函数
main "$@"
