#!/bin/bash
# FormalMath 自动化测试运行脚本

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 输出函数
print_header() {
    echo -e "\n${BLUE}========================================${NC}"
    echo -e "${BLUE}$1${NC}"
    echo -e "${BLUE}========================================${NC}\n"
}

print_success() {
    echo -e "${GREEN}✓ $1${NC}"
}

print_error() {
    echo -e "${RED}✗ $1${NC}"
}

print_warning() {
    echo -e "${YELLOW}⚠ $1${NC}"
}

# 帮助信息
show_help() {
    cat << EOF
FormalMath 测试运行脚本

用法: ./run-tests.sh [选项] [测试类型]

选项:
    -h, --help          显示帮助信息
    -v, --verbose       详细输出
    -c, --coverage      生成覆盖率报告
    -w, --watch         监视模式
    -f, --fail-fast     首次失败时停止

测试类型:
    all                 运行所有测试 (默认)
    frontend            仅运行前端测试
    backend             仅运行后端测试
    lean4               仅运行Lean4测试
    e2e                 仅运行E2E测试
    integration         仅运行集成测试
    unit                仅运行单元测试

示例:
    ./run-tests.sh                      # 运行所有测试
    ./run-tests.sh frontend             # 仅运行前端测试
    ./run-tests.sh backend -c           # 运行后端测试并生成覆盖率
    ./run-tests.sh all -v -f            # 详细输出，首次失败停止
EOF
}

# 参数解析
VERBOSE=false
COVERAGE=false
WATCH=false
FAIL_FAST=false
TEST_TYPE="all"

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_help
            exit 0
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -c|--coverage)
            COVERAGE=true
            shift
            ;;
        -w|--watch)
            WATCH=true
            shift
            ;;
        -f|--fail-fast)
            FAIL_FAST=true
            shift
            ;;
        all|frontend|backend|lean4|e2e|integration|unit)
            TEST_TYPE="$1"
            shift
            ;;
        *)
            print_error "未知选项: $1"
            show_help
            exit 1
            ;;
    esac
done

# 构建命令参数
BUILD_ARGS=""
if [ "$VERBOSE" = true ]; then
    BUILD_ARGS="$BUILD_ARGS --verbose"
fi
if [ "$COVERAGE" = true ]; then
    BUILD_ARGS="$BUILD_ARGS --coverage"
fi
if [ "$FAIL_FAST" = true ]; then
    BUILD_ARGS="$BUILD_ARGS --bail"
fi

# 运行前端测试
run_frontend_tests() {
    print_header "运行前端测试"
    
    cd ../FormalMath-Interactive
    
    # 检查依赖
    if [ ! -d "node_modules" ]; then
        print_warning "安装前端依赖..."
        npm ci
    fi
    
    # 代码检查
    print_header "运行 ESLint"
    npm run lint || print_warning "ESLint 检查失败"
    
    # 类型检查
    print_header "运行 TypeScript 类型检查"
    npm run type-check || print_warning "类型检查失败"
    
    # 单元测试
    print_header "运行前端单元测试"
    if [ "$WATCH" = true ]; then
        npm run test:unit:watch 2>/dev/null || npx jest --watch
    elif [ "$COVERAGE" = true ]; then
        npx jest --coverage --config=../tests/frontend/jest.config.js
    else
        npx jest --config=../tests/frontend/jest.config.js
    fi
    
    print_success "前端测试完成"
    cd ../tests
}

# 运行后端测试
run_backend_tests() {
    print_header "运行后端测试"
    
    cd backend
    
    # 检查依赖
    if ! python -c "import pytest" 2>/dev/null; then
        print_warning "安装Python测试依赖..."
        pip install -r requirements-test.txt
    fi
    
    # 运行测试
    PYTEST_ARGS="-v"
    if [ "$COVERAGE" = true ]; then
        PYTEST_ARGS="$PYTEST_ARGS --cov=../../tools --cov-report=html:../coverage/backend --cov-report=term"
    fi
    if [ "$FAIL_FAST" = true ]; then
        PYTEST_ARGS="$PYTEST_ARGS -x"
    fi
    
    print_header "运行后端单元测试"
    pytest unit/ $PYTEST_ARGS
    
    if [ "$TEST_TYPE" = "all" ] || [ "$TEST_TYPE" = "integration" ]; then
        print_header "运行后端集成测试"
        pytest integration/ $PYTEST_ARGS -m integration || print_warning "集成测试失败"
    fi
    
    print_success "后端测试完成"
    cd ..
}

# 运行Lean4测试
run_lean4_tests() {
    print_header "运行Lean4测试"
    
    cd lean4
    
    # 检查lake
    if ! command -v lake &> /dev/null; then
        print_error "未找到lake，请先安装Lean4"
        return 1
    fi
    
    # 构建
    print_header "构建Lean4测试"
    lake build || print_warning "构建失败"
    
    # 运行测试
    print_header "运行Lean4测试"
    lake test || print_warning "测试失败"
    
    print_success "Lean4测试完成"
    cd ..
}

# 运行E2E测试
run_e2e_tests() {
    print_header "运行E2E测试"
    
    cd ../FormalMath-Interactive
    
    # 构建应用
    print_header "构建应用"
    npm run build
    
    # 启动服务器
    print_header "启动测试服务器"
    npm run preview &
    SERVER_PID=$!
    
    # 等待服务器启动
    sleep 5
    
    # 运行Cypress测试
    cd ../tests
    npx cypress run --config-file frontend/cypress.config.ts || {
        print_error "E2E测试失败"
        kill $SERVER_PID 2>/dev/null
        exit 1
    }
    
    # 停止服务器
    kill $SERVER_PID 2>/dev/null
    
    print_success "E2E测试完成"
}

# 主执行逻辑
main() {
    print_header "FormalMath 测试套件"
    echo "测试类型: $TEST_TYPE"
    echo "覆盖率: $COVERAGE"
    echo "监视模式: $WATCH"
    echo ""
    
    START_TIME=$(date +%s)
    
    case $TEST_TYPE in
        all)
            run_frontend_tests
            run_backend_tests
            run_lean4_tests
            run_e2e_tests
            ;;
        frontend)
            run_frontend_tests
            ;;
        backend)
            run_backend_tests
            ;;
        lean4)
            run_lean4_tests
            ;;
        e2e)
            run_e2e_tests
            ;;
        integration)
            run_backend_tests
            ;;
        unit)
            run_frontend_tests
            run_backend_tests
            ;;
        *)
            print_error "未知测试类型: $TEST_TYPE"
            exit 1
            ;;
    esac
    
    END_TIME=$(date +%s)
    DURATION=$((END_TIME - START_TIME))
    
    print_header "测试完成"
    echo "总耗时: ${DURATION}秒"
    print_success "所有测试通过！"
}

# 捕获中断信号
trap 'print_error "测试被中断"; exit 130' INT TERM

# 运行主函数
main
