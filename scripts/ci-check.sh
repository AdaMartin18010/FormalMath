#!/bin/bash
# =============================================================================
# FormalMath 本地CI检查脚本 (Linux/Mac)
# 描述: 在本地运行类似CI的检查，帮助开发者在提交前发现问题
# 使用方法: ./scripts/ci-check.sh [选项]
# =============================================================================

set -e  # 遇到错误立即退出

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 默认配置
CHECK_MARKDOWN=true
CHECK_PYTHON=true
CHECK_LINKS=false
CHECK_LEAN=false
FIX_MODE=false
VERBOSE=false

# 计数器
ERRORS=0
WARNINGS=0

# 帮助信息
show_help() {
    cat << EOF
FormalMath 本地CI检查脚本

使用方法: $0 [选项]

选项:
    -h, --help          显示此帮助信息
    -m, --markdown      仅检查Markdown格式
    -p, --python        仅检查Python脚本
    -l, --links         检查链接有效性
    -L, --lean          检查Lean4代码
    -a, --all           运行所有检查（包括链接和Lean）
    -f, --fix           自动修复可修复的问题
    -v, --verbose       显示详细输出
    -q, --quick         快速模式（仅关键检查）

示例:
    $0                  # 运行默认检查
    $0 --all            # 运行所有检查
    $0 --fix            # 自动修复格式问题
    $0 -m -p            # 仅检查Markdown和Python
EOF
}

# 解析参数
while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_help
            exit 0
            ;;
        -m|--markdown)
            CHECK_PYTHON=false
            CHECK_LINKS=false
            CHECK_LEAN=false
            shift
            ;;
        -p|--python)
            CHECK_MARKDOWN=false
            CHECK_LINKS=false
            CHECK_LEAN=false
            shift
            ;;
        -l|--links)
            CHECK_LINKS=true
            shift
            ;;
        -L|--lean)
            CHECK_LEAN=true
            shift
            ;;
        -a|--all)
            CHECK_LINKS=true
            CHECK_LEAN=true
            shift
            ;;
        -f|--fix)
            FIX_MODE=true
            shift
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -q|--quick)
            CHECK_LINKS=false
            CHECK_LEAN=false
            shift
            ;;
        *)
            echo -e "${RED}未知选项: $1${NC}"
            show_help
            exit 1
            ;;
    esac
done

# 打印标题
print_header() {
    echo ""
    echo -e "${BLUE}══════════════════════════════════════════════════════════════${NC}"
    echo -e "${BLUE}  $1${NC}"
    echo -e "${BLUE}══════════════════════════════════════════════════════════════${NC}"
}

# 打印成功信息
print_success() {
    echo -e "${GREEN}✅ $1${NC}"
}

# 打印警告信息
print_warning() {
    echo -e "${YELLOW}⚠️  $1${NC}"
    ((WARNINGS++))
}

# 打印错误信息
print_error() {
    echo -e "${RED}❌ $1${NC}"
    ((ERRORS++))
}

# 打印信息
print_info() {
    if [ "$VERBOSE" = true ]; then
        echo -e "  $1"
    fi
}

# 检查命令是否存在
check_command() {
    if ! command -v $1 &> /dev/null; then
        return 1
    fi
    return 0
}

# ==================== Markdown格式检查 ====================
check_markdown() {
    print_header "检查 Markdown 格式"
    
    # 检查markdownlint-cli
    if check_command markdownlint; then
        echo "🔍 使用 markdownlint 检查..."
        
        if [ "$FIX_MODE" = true ] && check_command markdownlint-fix; then
            echo "  尝试自动修复..."
            markdownlint '**/*.md' --fix --ignore 'node_modules/**' --ignore '00-归档/**' --config .markdownlint.json 2>/dev/null || true
        fi
        
        # 运行检查
        if markdownlint '**/*.md' --ignore 'node_modules/**' --ignore '00-归档/**' --config .markdownlint.json > /tmp/md-lint.txt 2>&1; then
            print_success "Markdown格式检查通过"
        else
            print_warning "发现Markdown格式问题:"
            cat /tmp/md-lint.txt | head -20
            if [ $(wc -l < /tmp/md-lint.txt) -gt 20 ]; then
                echo "  ... (还有 $(($(wc -l < /tmp/md-lint.txt) - 20)) 个问题)"
            fi
        fi
    else
        # 使用简单的自定义检查
        echo "⚠️  markdownlint 未安装，使用基础检查..."
        echo "   安装: npm install -g markdownlint-cli"
        
        # 检查文件是否以空行结尾
        local files_no_newline=0
        while IFS= read -r file; do
            if [ -n "$(tail -c 1 "$file")" ]; then
                print_info "$file 缺少末尾空行"
                ((files_no_newline++))
            fi
        done < <(find . -name "*.md" -not -path "./node_modules/*" -not -path "./00-归档/*")
        
        if [ $files_no_newline -eq 0 ]; then
            print_success "基础Markdown检查通过"
        else
            print_warning "$files_no_newline 个文件缺少末尾空行"
        fi
    fi
}

# ==================== Python脚本检查 ====================
check_python() {
    print_header "检查 Python 脚本"
    
    # 检查Python是否可用
    if ! check_command python3; then
        print_error "Python3 未安装"
        return
    fi
    
    # 语法检查
    echo "🔍 检查Python语法..."
    if python3 -m compileall tools/ -q 2>/dev/null; then
        print_success "Python语法检查通过"
    else
        print_error "发现Python语法错误"
    fi
    
    # 检查flake8
    if check_command flake8; then
        echo "🔍 使用 flake8 检查代码风格..."
        if flake8 tools/ --count --select=E9,F63,F7,F82 --show-source --statistics 2>/dev/null; then
            print_success "flake8基础检查通过"
        else
            print_warning "flake8发现代码风格问题"
        fi
    else
        print_info "flake8 未安装，跳过代码风格检查"
        print_info "安装: pip install flake8"
    fi
    
    # 检查black
    if check_command black; then
        echo "🔍 使用 Black 检查代码格式..."
        if [ "$FIX_MODE" = true ]; then
            echo "  自动格式化..."
            black tools/ --quiet 2>/dev/null || true
            print_success "代码格式化完成"
        elif black --check --diff tools/ 2>/dev/null; then
            print_success "Black格式检查通过"
        else
            print_warning "代码格式不符合Black标准 (运行 --fix 自动修复)"
        fi
    else
        print_info "black 未安装，跳过代码格式检查"
    fi
    
    # 运行单元测试（如果有）
    if [ -d "tests" ] && check_command pytest; then
        echo "🧪 运行单元测试..."
        if pytest tests/ -q --tb=short 2>/dev/null; then
            print_success "单元测试通过"
        else
            print_error "单元测试失败"
        fi
    fi
}

# ==================== 链接检查 ====================
check_links() {
    print_header "检查链接有效性"
    
    if [ -f "tools/link_checker.py" ]; then
        echo "🔍 使用 link_checker.py 检查..."
        if python3 tools/link_checker.py --internal-only 2>/dev/null; then
            print_success "内部链接检查通过"
        else
            print_warning "发现链接问题"
        fi
    else
        # 基础链接检查
        echo "🔍 运行基础链接检查..."
        python3 << 'EOF'
import re
import sys
from pathlib import Path

def check_links():
    issues = []
    md_files = list(Path('.').rglob('*.md'))
    
    for md_file in md_files:
        if 'node_modules' in str(md_file) or '00-归档' in str(md_file):
            continue
        
        content = md_file.read_text(encoding='utf-8')
        links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
        
        for text, link in links:
            if link.startswith('http') or link.startswith('#'):
                continue
            
            target = md_file.parent / link.split('#')[0]
            if link.startswith('./'):
                target = md_file.parent / link[2:].split('#')[0]
            
            if not target.exists() and not target.with_suffix('.md').exists():
                issues.append(f"{md_file}: 链接 '{link}' 无效")
    
    if issues:
        print(f"⚠️  发现 {len(issues)} 个链接问题:")
        for issue in issues[:10]:
            print(f"  - {issue}")
        if len(issues) > 10:
            print(f"  ... 还有 {len(issues) - 10} 个问题")
        return 1
    else:
        print("✅ 所有内部链接有效")
        return 0

sys.exit(check_links())
EOF
    fi
}

# ==================== Lean代码检查 ====================
check_lean() {
    print_header "检查 Lean4 代码"
    
    if ! check_command lean; then
        print_warning "Lean4 未安装，跳过检查"
        print_info "安装: https://leanprover.github.io/lean4/doc/quickstart.html"
        return
    fi
    
    echo "🔍 编译Lean文件..."
    local failed=0
    while IFS= read -r file; do
        if ! lean "$file" 2>/dev/null; then
            print_error "编译失败: $file"
            ((failed++))
        fi
    done < <(find . -name "*.lean" -not -path "./.lake/*" 2>/dev/null)
    
    if [ $failed -eq 0 ]; then
        print_success "所有Lean文件编译成功"
    else
        print_error "$failed 个Lean文件编译失败"
    fi
}

# ==================== 主程序 ====================
main() {
    echo ""
    echo -e "${BLUE}╔══════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${BLUE}║          FormalMath 本地CI检查                              ║${NC}"
    echo -e "${BLUE}╚══════════════════════════════════════════════════════════════╝${NC}"
    echo ""
    
    # 获取项目根目录
    SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
    cd "$SCRIPT_DIR/.."
    
    echo "📁 工作目录: $(pwd)"
    echo ""
    
    # 运行各项检查
    if [ "$CHECK_MARKDOWN" = true ]; then
        check_markdown
    fi
    
    if [ "$CHECK_PYTHON" = true ]; then
        check_python
    fi
    
    if [ "$CHECK_LINKS" = true ]; then
        check_links
    fi
    
    if [ "$CHECK_LEAN" = true ]; then
        check_lean
    fi
    
    # 输出汇总
    echo ""
    echo -e "${BLUE}══════════════════════════════════════════════════════════════${NC}"
    echo -e "${BLUE}  检查完成${NC}"
    echo -e "${BLUE}══════════════════════════════════════════════════════════════${NC}"
    echo ""
    
    if [ $ERRORS -eq 0 ] && [ $WARNINGS -eq 0 ]; then
        echo -e "${GREEN}🎉 所有检查通过！可以安全提交。${NC}"
        exit 0
    else
        if [ $ERRORS -gt 0 ]; then
            echo -e "${RED}❌ 发现 $ERRORS 个错误${NC}"
        fi
        if [ $WARNINGS -gt 0 ]; then
            echo -e "${YELLOW}⚠️  发现 $WARNINGS 个警告${NC}"
        fi
        echo ""
        if [ $ERRORS -gt 0 ]; then
            echo -e "${RED}请修复错误后再提交。${NC}"
            exit 1
        else
            echo -e "${YELLOW}建议修复警告，但不是必须。${NC}"
            exit 0
        fi
    fi
}

# 运行主程序
main
