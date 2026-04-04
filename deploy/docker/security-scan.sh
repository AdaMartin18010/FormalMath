#!/bin/bash
# ============================================
# Docker镜像安全扫描脚本
# 使用Trivy进行漏洞扫描
# ============================================

set -euo pipefail

# 配置
IMAGES=(
    "formalmath/backend:latest"
    "formalmath/frontend:latest"
)

SEVERITY="HIGH,CRITICAL"
EXIT_CODE=0

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo "=============================================="
echo "FormalMath Docker镜像安全扫描"
echo "时间: $(date)"
echo "=============================================="

# 检查trivy是否安装
if ! command -v trivy &> /dev/null; then
    echo -e "${YELLOW}Trivy未安装，正在安装...${NC}"
    curl -sfL https://raw.githubusercontent.com/aquasecurity/trivy/main/contrib/install.sh | sh -s -- -b /usr/local/bin
fi

# 扫描每个镜像
for image in "${IMAGES[@]}"; do
    echo ""
    echo "----------------------------------------------"
    echo "扫描镜像: $image"
    echo "----------------------------------------------"
    
    # 检查镜像是否存在
    if ! docker image inspect "$image" &> /dev/null; then
        echo -e "${YELLOW}镜像不存在: $image${NC}"
        continue
    fi
    
    # 执行扫描
    if trivy image --severity "$SEVERITY" --exit-code 1 --no-progress "$image"; then
        echo -e "${GREEN}✓ $image 扫描通过${NC}"
    else
        echo -e "${RED}✗ $image 发现漏洞${NC}"
        EXIT_CODE=1
    fi
done

echo ""
echo "=============================================="
if [ $EXIT_CODE -eq 0 ]; then
    echo -e "${GREEN}所有镜像扫描通过！${NC}"
else
    echo -e "${RED}发现安全漏洞，请修复后再部署！${NC}"
fi
echo "=============================================="

exit $EXIT_CODE
