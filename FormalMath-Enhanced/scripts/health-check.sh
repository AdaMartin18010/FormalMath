#!/bin/bash
# FormalMath - 健康检查脚本

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# 配置
API_URL="http://localhost/api/v1"
FRONTEND_URL="http://localhost"
TIMEOUT=10

echo "=========================================="
echo "FormalMath 健康检查"
echo "=========================================="
echo ""

# 检查函数
check_service() {
    local name=$1
    local url=$2
    local expected_code=${3:-200}
    
    echo -n "检查 $name ... "
    
    if response=$(curl -s -o /dev/null -w "%{http_code}" --max-time $TIMEOUT "$url" 2>/dev/null); then
        if [ "$response" = "$expected_code" ]; then
            echo -e "${GREEN}✓ 正常${NC} (HTTP $response)"
            return 0
        else
            echo -e "${RED}✗ 异常${NC} (HTTP $response, 期望 $expected_code)"
            return 1
        fi
    else
        echo -e "${RED}✗ 无法连接${NC}"
        return 1
    fi
}

# 检查Docker容器
echo "Docker容器状态:"
echo "----------------------------------------"
docker-compose ps --format "table {{.Name}}\t{{.State}}\t{{.Status}}"
echo ""

# 检查服务
echo "服务健康检查:"
echo "----------------------------------------"

failed=0

# Nginx
if ! check_service "Nginx" "$FRONTEND_URL/health"; then
    failed=1
fi

# 后端API
if ! check_service "后端API" "$API_URL/health"; then
    failed=1
fi

# API文档
if ! check_service "API文档" "$FRONTEND_URL/docs"; then
    failed=1
fi

# Redis
echo -n "检查 Redis ... "
if docker-compose exec -T redis redis-cli ping | grep -q "PONG"; then
    echo -e "${GREEN}✓ 正常${NC}"
else
    echo -e "${RED}✗ 异常${NC}"
    failed=1
fi

echo ""

# 检查资源使用
echo "资源使用情况:"
echo "----------------------------------------"
docker stats --no-stream --format "table {{.Name}}\t{{.CPUPerc}}\t{{.MemUsage}}\t{{.NetIO}}"
echo ""

# 总结
echo "=========================================="
if [ $failed -eq 0 ]; then
    echo -e "${GREEN}✓ 所有检查通过${NC}"
    exit 0
else
    echo -e "${RED}✗ 存在异常服务${NC}"
    echo ""
    echo "查看日志: docker-compose logs -f [service-name]"
    exit 1
fi
