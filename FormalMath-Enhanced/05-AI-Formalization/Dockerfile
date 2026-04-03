# Lean4 + Python AI形式化数学环境
# 基于Ubuntu 22.04

FROM ubuntu:22.04

# 设置环境变量
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC
ENV PATH="/root/.elan/bin:/root/.local/bin:${PATH}"
ENV LEAN_VERSION="4.5.0"
ENV MATHLIB_VERSION="v4.5.0"

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    curl \
    git \
    wget \
    python3.10 \
    python3-pip \
    python3.10-venv \
    build-essential \
    cmake \
    clang \
    llvm \
    libgmp-dev \
    libmpfr-dev \
    libmpc-dev \
    pkg-config \
    vim \
    nano \
    jq \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 安装Elan（Lean版本管理器）
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# 安装指定版本的Lean
RUN elan toolchain install ${LEAN_VERSION} && \
    elan default ${LEAN_VERSION}

# 安装Lake（Lean包管理器）
RUN elan run ${LEAN_VERSION} lake --version

# 创建项目目录
WORKDIR /workspace

# 创建Lean项目结构
RUN mkdir -p /workspace/lean_project
WORKDIR /workspace/lean_project

# 初始化Lake项目
RUN lake init formalmath

# 配置lakefile.lean以包含Mathlib4
RUN cat > lakefile.lean << 'EOF'
import Lake
open Lake DSL

package "formalmath" where
  version := "0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.5.0"

@[default_target]
lean_lib «Formalmath» where
  globs := #[.submodules `Formalmath]
EOF

# 更新项目配置并获取依赖
RUN lake update && \
    lake exe cache get || true

# 构建项目（这可能需要一段时间）
RUN lake build || true

# 安装Python依赖
WORKDIR /workspace
COPY requirements.txt /workspace/requirements.txt

# 如果没有requirements.txt，创建一个
RUN if [ ! -f /workspace/requirements.txt ]; then \
    cat > /workspace/requirements.txt << 'EOF'
# 基础依赖
numpy>=1.24.0
pandas>=2.0.0
requests>=2.31.0
urllib3>=2.0.0

# API和Web
openai>=1.0.0
anthropic>=0.8.0
httpx>=0.25.0

# 数据处理和科学计算
scipy>=1.11.0
scikit-learn>=1.3.0
matplotlib>=3.7.0
seaborn>=0.12.0

# Jupyter环境
jupyter>=1.0.0
jupyterlab>=4.0.0
ipywidgets>=8.0.0
notebook>=7.0.0

# 工具和辅助
python-dotenv>=1.0.0
pyyaml>=6.0.0
tqdm>=4.65.0
rich>=13.0.0
click>=8.1.0

# 测试
test>=0.1.0
pytest>=7.4.0
pytest-cov>=4.1.0
EOF
    fi

# 安装Python包
RUN pip3 install --no-cache-dir -r /workspace/requirements.txt

# 设置Python环境变量
ENV PYTHONPATH="/workspace/tools:${PYTHONPATH}"

# 创建工作目录结构
RUN mkdir -p /workspace/tools \
    /workspace/examples \
    /workspace/data \
    /workspace/output \
    /workspace/models

# 复制工具代码
COPY tools/*.py /workspace/tools/

# 复制示例
COPY examples/*.ipynb /workspace/examples/

# 创建启动脚本
RUN cat > /workspace/start.sh << 'EOF'
#!/bin/bash

echo "========================================"
echo "AI Formalization Math Environment"
echo "========================================"
echo ""
echo "Available commands:"
echo "  lake --version     - Check Lean version"
echo "  python3            - Python interpreter"
echo "  jupyter lab        - Start Jupyter Lab"
echo "  python3 /workspace/tools/auto_formalize.py - Interactive mode"
echo ""
echo "Environment variables:"
echo "  DEEPSEEK_API_KEY   - Set your DeepSeek API key"
echo "  LEAN_PROJECT_PATH  - Lean project path (/workspace/lean_project)"
echo ""
echo "========================================"

# 检查API密钥
if [ -z "$DEEPSEEK_API_KEY" ]; then
    echo "⚠️  Warning: DEEPSEEK_API_KEY not set"
    echo "   Set it with: export DEEPSEEK_API_KEY=your_key"
fi

# 启动指定的命令，或默认bash
if [ $# -eq 0 ]; then
    exec bash
else
    exec "$@"
fi
EOF

RUN chmod +x /workspace/start.sh

# 健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=60s --retries=3 \
    CMD lake --version && python3 --version || exit 1

# 暴露Jupyter端口
EXPOSE 8888

# 设置默认工作目录
WORKDIR /workspace

# 入口点
ENTRYPOINT ["/workspace/start.sh"]
CMD ["bash"]
