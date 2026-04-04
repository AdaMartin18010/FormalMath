#!/bin/bash
# FormalMath-Enhanced 监控系统健康检查脚本

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# 状态计数
OK_COUNT=0
WARN_COUNT=0
ERROR_COUNT=0

# 检查函数
check_service() {
    local name=$1
    local url=$2
    local expected_status=${3:-200}
    
    echo -n "检查 $name ... "
    
    if response=$(curl -s -o /dev/null -w "%{http_code}" "$url" 2>/dev/null); then
        if [ "$response" = "$expected_status" ]; then
            echo -e "${GREEN}OK${NC} (HTTP $response)"
            OK_COUNT=$((OK_COUNT + 1))
            return 0
        else
            echo -e "${YELLOW}WARN${NC} (HTTP $response, expected $expected_status)"
            WARN_COUNT=$((WARN_COUNT + 1))
            return 1
        fi
    else
        echo -e "${RED}ERROR${NC} (无法连接)"
        ERROR_COUNT=$((ERROR_COUNT + 1))
        return 1
    fi
}

# 检查容器
check_container() {
    local name=$1
    
    echo -n "检查容器 $name ... "
    
    if docker ps --format "{{.Names}}" | grep -q "^${name}$"; then
        local status=$(docker inspect --format="{{.State.Status}}" "$name" 2>/dev/null)
        
        if [ "$status" = "running" ]; then
            echo -e "${GREEN}OK${NC} (状态: $status)"
            OK_COUNT=$((OK_COUNT + 1))
            return 0
        else
            echo -e "${RED}ERROR${NC} (状态: $status)"
            ERROR_COUNT=$((ERROR_COUNT + 1))
            return 1
        fi
    else
        echo -e "${RED}ERROR${NC} (容器不存在)"
        ERROR_COUNT=$((ERROR_COUNT + 1))
        return 1
    fi
}

# 主检查流程
echo "=========================================="
echo "FormalMath 监控系统健康检查"
echo "=========================================="
echo ""

# 检查核心组件
echo -e "${BLUE}[核心服务]${NC}"
check_service "Prometheus" "http://localhost:9090/-/healthy"
check_service "Grafana" "http://localhost:3000/api/health"
check_service "Alertmanager" "http://localhost:9093/-/healthy"
check_service "Elasticsearch" "http://localhost:9200/_cluster/health"
check_service "Kibana" "http://localhost:5601/api/status"
echo ""

# 检查容器状态
echo -e "${BLUE}[容器状态]${NC}"
check_container "formalmath-prometheus"
check_container "formalmath-grafana"
check_container "formalmath-alertmanager"
check_container "formalmath-elasticsearch"
check_container "formalmath-kibana"
echo ""

# 检查结果汇总
echo "=========================================="
echo -e "检查结果汇总:"
echo -e "  ${GREEN}正常: $OK_COUNT${NC}"
echo -e "  ${YELLOW}警告: $WARN_COUNT${NC}"
echo -e "  ${RED}错误: $ERROR_COUNT${NC}"
echo "=========================================="

# 退出码
if [ $ERROR_COUNT -gt 0 ]; then
    exit 2
elif [ $WARN_COUNT -gt 0 ]; then
    exit 1
else
    exit 0
fi
