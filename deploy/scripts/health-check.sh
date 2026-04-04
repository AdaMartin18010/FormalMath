#!/bin/bash
# ============================================
# FormalMath - 健康检查脚本
# 用于验证部署后的服务状态
# ============================================

set -euo pipefail

# 配置
BACKEND_URL="${BACKEND_URL:-http://localhost:8000}"
FRONTEND_URL="${FRONTEND_URL:-http://localhost:80}"
TIMEOUT=10
EXIT_CODE=0

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# 日志函数
log_info() { echo -e "${BLUE}[INFO]${NC} $1"; }
log_success() { echo -e "${GREEN}[PASS]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[FAIL]${NC} $1"; }

# 检查HTTP端点
check_endpoint() {
    local name=$1
    local url=$2
    local expected_code=${3:-200}
    
    log_info "检查 $name ($url)..."
    
    local response
    local http_code
    
    response=$(curl -s -o /dev/null -w "%{http_code}" --max-time $TIMEOUT "$url" 2>/dev/null || echo "000")
    
    if [ "$response" = "$expected_code" ]; then
        log_success "$name 响应正常 (HTTP $response)"
        return 0
    else
        log_error "$name 响应异常 (HTTP $response, 期望 $expected_code)"
        return 1
    fi
}

# 检查JSON端点
check_json_endpoint() {
    local name=$1
    local url=$2
    local jq_filter=${3:-}
    
    log_info "检查 $name ($url)..."
    
    local response
    response=$(curl -s --max-time $TIMEOUT "$url" 2>/dev/null || echo "")
    
    if [ -z "$response" ]; then
        log_error "$name 无响应"
        return 1
    fi
    
    if ! echo "$response" | jq -e . > /dev/null 2>&1; then
        log_error "$name 返回非JSON数据"
        return 1
    fi
    
    if [ -n "$jq_filter" ]; then
        if echo "$response" | jq -e "$jq_filter" > /dev/null 2>&1; then
            log_success "$name 响应正常"
            return 0
        else
            log_error "$name 响应不符合预期"
            return 1
        fi
    else
        log_success "$name 响应正常 (JSON)"
        return 0
    fi
}

# 主函数
main() {
    echo "=============================================="
    echo "FormalMath 健康检查"
    echo "时间: $(date)"
    echo "=============================================="
    echo ""
    
    # 检查后端
    echo "--- 后端服务检查 ---"
    check_json_endpoint "后端健康检查" "$BACKEND_URL/health" '.status == "healthy"' || EXIT_CODE=1
    check_endpoint "API文档" "$BACKEND_URL/docs" 200 || EXIT_CODE=1
    check_endpoint "API OpenAPI" "$BACKEND_URL/openapi.json" 200 || EXIT_CODE=1
    echo ""
    
    # 检查前端
    echo "--- 前端服务检查 ---"
    check_endpoint "前端首页" "$FRONTEND_URL/" 200 || EXIT_CODE=1
    check_endpoint "前端健康检查" "$FRONTEND_URL/health" 200 || EXIT_CODE=1
    echo ""
    
    # 检查关键API
    echo "--- 关键API检查 ---"
    check_json_endpoint "概念列表API" "$BACKEND_URL/api/v1/concepts" '.data' || EXIT_CODE=1
    check_json_endpoint "数学家列表API" "$BACKEND_URL/api/v1/mathematicians" '.data' || EXIT_CODE=1
    echo ""
    
    # 性能检查
    echo "--- 性能检查 ---"
    log_info "测试API响应时间..."
    
    local response_time
    response_time=$(curl -s -o /dev/null -w "%{time_total}" --max-time $TIMEOUT "$BACKEND_URL/health" 2>/dev/null || echo "999")
    
    # 转换为毫秒
    local response_ms
    response_ms=$(echo "$response_time * 1000" | bc 2>/dev/null || echo "999999")
    response_ms=${response_ms%.*}
    
    if [ "$response_ms" -lt 500 ]; then
        log_success "API响应时间正常 (${response_ms}ms)"
    elif [ "$response_ms" -lt 1000 ]; then
        log_warn "API响应时间较慢 (${response_ms}ms)"
    else
        log_error "API响应时间过长 (${response_ms}ms)"
        EXIT_CODE=1
    fi
    echo ""
    
    # 总结
    echo "=============================================="
    if [ $EXIT_CODE -eq 0 ]; then
        log_success "所有健康检查通过！"
    else
        log_error "部分健康检查失败，请检查服务状态"
    fi
    echo "=============================================="
    
    return $EXIT_CODE
}

# 运行主函数
main "$@"
