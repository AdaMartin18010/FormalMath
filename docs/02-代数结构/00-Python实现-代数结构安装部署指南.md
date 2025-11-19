# 代数结构Python实现安装与部署指南

## 概述

本文档提供代数结构Python实现体系的完整安装、配置和部署指南，包括环境要求、依赖安装、项目配置、测试验证和部署方案。

## 1. 系统要求

### 1.1 Python版本

- **最低版本**: Python 3.8
- **推荐版本**: Python 3.10 或更高
- **测试版本**: Python 3.8, 3.9, 3.10, 3.11, 3.12

### 1.2 操作系统

- **Windows**: Windows 10 或更高版本
- **Linux**: Ubuntu 20.04+, Debian 11+, CentOS 8+
- **macOS**: macOS 10.15 (Catalina) 或更高版本

### 1.3 硬件要求

- **CPU**: 双核或更高（推荐四核）
- **内存**: 4GB RAM（推荐8GB或更高）
- **存储**: 至少500MB可用空间
- **GPU**: 可选，用于加速计算（需要CUDA支持）

## 2. 依赖安装

### 2.1 核心依赖

创建 `requirements.txt` 文件：

```text
# 核心数值计算库
numpy>=1.20.0
scipy>=1.7.0

# 可视化库
matplotlib>=3.3.0
networkx>=2.5

# 符号计算库
sympy>=1.7.0

# Web框架（可选）
flask>=2.0.0
flask-restful>=0.3.9

# 数据库（可选）
sqlalchemy>=1.4.0

# 测试框架
pytest>=6.2.0
pytest-cov>=2.12.0

# 文档生成（可选）
sphinx>=4.0.0
sphinx-rtd-theme>=0.5.0

# 代码质量（可选）
black>=21.0.0
flake8>=3.9.0
mypy>=0.910
```

### 2.2 可选依赖

```text
# GPU加速（可选）
cupy-cuda11x>=10.0.0  # 根据CUDA版本选择

# 并行计算（可选）
joblib>=1.0.0

# 性能分析（可选）
line-profiler>=3.0.0
memory-profiler>=0.60.0

# Jupyter支持（可选）
jupyter>=1.0.0
ipython>=7.0.0
```

### 2.3 安装步骤

#### 方法1: 使用pip安装

```bash
# 创建虚拟环境（推荐）
python -m venv venv

# 激活虚拟环境
# Windows:
venv\Scripts\activate
# Linux/macOS:
source venv/bin/activate

# 安装依赖
pip install -r requirements.txt

# 或安装可选依赖
pip install -r requirements.txt -r requirements-optional.txt
```

#### 方法2: 使用conda安装

```bash
# 创建conda环境
conda create -n algebraic-structures python=3.10
conda activate algebraic-structures

# 安装核心依赖
conda install numpy scipy matplotlib networkx sympy

# 安装其他依赖
pip install flask flask-restful pytest
```

#### 方法3: 使用poetry安装

```bash
# 安装poetry
curl -sSL https://install.python-poetry.org | python3 -

# 初始化项目
poetry init

# 安装依赖
poetry install
```

## 3. 项目结构

### 3.1 推荐目录结构

```text
algebraic_structures/
├── README.md
├── requirements.txt
├── setup.py
├── pyproject.toml
├── .gitignore
├── .pylintrc
├── docs/
│   ├── api/
│   ├── tutorials/
│   └── examples/
├── src/
│   └── algebraic_structures/
│       ├── __init__.py
│       ├── group_theory/
│       │   ├── __init__.py
│       │   ├── groups.py
│       │   ├── representations.py
│       │   └── actions.py
│       ├── ring_theory/
│       │   ├── __init__.py
│       │   ├── rings.py
│       │   └── ideals.py
│       ├── field_theory/
│       │   ├── __init__.py
│       │   └── fields.py
│       ├── module_theory/
│       │   ├── __init__.py
│       │   └── modules.py
│       ├── lie_algebra/
│       │   ├── __init__.py
│       │   └── lie_algebras.py
│       ├── representation_theory/
│       │   ├── __init__.py
│       │   └── representations.py
│       ├── category_theory/
│       │   ├── __init__.py
│       │   └── categories.py
│       ├── linear_algebra/
│       │   ├── __init__.py
│       │   └── matrices.py
│       └── tools/
│           ├── __init__.py
│           ├── calculator.py
│           ├── analyzer.py
│           └── visualizer.py
├── tests/
│   ├── __init__.py
│   ├── test_groups.py
│   ├── test_rings.py
│   ├── test_fields.py
│   └── test_tools.py
└── examples/
    ├── cryptography/
    ├── coding_theory/
    └── physics/
```

### 3.2 setup.py配置

```python
from setuptools import setup, find_packages

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

with open("requirements.txt", "r", encoding="utf-8") as fh:
    requirements = [line.strip() for line in fh if line.strip() and not line.startswith("#")]

setup(
    name="algebraic-structures",
    version="1.0.0",
    author="FormalMath Project",
    author_email="info@formalmath.org",
    description="Python实现代数结构综合工具库",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/formalmath/algebraic-structures",
    packages=find_packages(where="src"),
    package_dir={"": "src"},
    classifiers=[
        "Development Status :: 4 - Beta",
        "Intended Audience :: Education",
        "Intended Audience :: Science/Research",
        "Topic :: Scientific/Engineering :: Mathematics",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
    ],
    python_requires=">=3.8",
    install_requires=requirements,
    extras_require={
        "dev": [
            "pytest>=6.2.0",
            "pytest-cov>=2.12.0",
            "black>=21.0.0",
            "flake8>=3.9.0",
            "mypy>=0.910",
        ],
        "gpu": [
            "cupy-cuda11x>=10.0.0",
        ],
        "web": [
            "flask>=2.0.0",
            "flask-restful>=0.3.9",
        ],
    },
    entry_points={
        "console_scripts": [
            "algstruct=algebraic_structures.tools.cli:main",
        ],
    },
)
```

## 4. 安装验证

### 4.1 基本验证

```python
# test_installation.py
"""验证安装是否成功"""

def test_imports():
    """测试所有模块导入"""
    try:
        from algebraic_structures.group_theory import FiniteGroup
        from algebraic_structures.ring_theory import Ring
        from algebraic_structures.field_theory import FiniteField
        from algebraic_structures.tools import UniversalAlgebraicCalculator
        print("✅ 所有模块导入成功")
        return True
    except ImportError as e:
        print(f"❌ 导入失败: {e}")
        return False

def test_basic_functionality():
    """测试基本功能"""
    try:
        from algebraic_structures.group_theory import cyclic_group

        G = cyclic_group(6)
        assert G.order() == 6
        print("✅ 基本功能测试通过")
        return True
    except Exception as e:
        print(f"❌ 功能测试失败: {e}")
        return False

if __name__ == "__main__":
    print("开始验证安装...")
    if test_imports() and test_basic_functionality():
        print("\n🎉 安装验证成功！")
    else:
        print("\n⚠️ 安装验证失败，请检查错误信息")
```

运行验证：

```bash
python test_installation.py
```

### 4.2 运行测试套件

```bash
# 运行所有测试
pytest tests/

# 运行特定测试
pytest tests/test_groups.py

# 运行测试并生成覆盖率报告
pytest tests/ --cov=algebraic_structures --cov-report=html

# 查看覆盖率报告
# 打开 htmlcov/index.html
```

## 5. 配置选项

### 5.1 配置文件

创建 `config.ini` 文件：

```ini
[general]
# 默认数值精度
precision = 15

# 缓存大小
cache_size = 128

# 并行计算线程数
num_threads = 4

[performance]
# 启用缓存
enable_cache = true

# 启用并行计算
enable_parallel = true

# GPU加速（如果可用）
enable_gpu = false

[visualization]
# 默认图形大小
figure_size = (10, 8)

# 默认DPI
dpi = 100

# 图形格式
format = png

[logging]
# 日志级别
level = INFO

# 日志文件
log_file = algebraic_structures.log
```

### 5.2 环境变量

```bash
# 设置数值精度
export ALGEBRAIC_STRUCTURES_PRECISION=15

# 设置缓存大小
export ALGEBRAIC_STRUCTURES_CACHE_SIZE=128

# 启用调试模式
export ALGEBRAIC_STRUCTURES_DEBUG=true

# 设置日志级别
export ALGEBRAIC_STRUCTURES_LOG_LEVEL=DEBUG
```

## 6. 开发环境设置

### 6.1 IDE配置

#### VS Code

创建 `.vscode/settings.json`:

```json
{
    "python.linting.enabled": true,
    "python.linting.pylintEnabled": true,
    "python.formatting.provider": "black",
    "python.testing.pytestEnabled": true,
    "python.testing.unittestEnabled": false,
    "[python]": {
        "editor.formatOnSave": true,
        "editor.codeActionsOnSave": {
            "source.organizeImports": true
        }
    }
}
```

#### PyCharm

1. 打开 Settings → Project → Python Interpreter
2. 选择虚拟环境
3. 启用 Code Inspection
4. 配置测试框架为 pytest

### 6.2 代码质量工具

```bash
# 格式化代码
black src/ tests/

# 检查代码风格
flake8 src/ tests/

# 类型检查
mypy src/

# 代码复杂度分析
radon cc src/
```

## 7. 部署方案

### 7.1 本地部署

```bash
# 1. 克隆或下载项目
git clone https://github.com/formalmath/algebraic-structures.git
cd algebraic-structures

# 2. 创建虚拟环境
python -m venv venv
source venv/bin/activate  # Linux/macOS
# 或
venv\Scripts\activate  # Windows

# 3. 安装依赖
pip install -r requirements.txt

# 4. 安装包
pip install -e .

# 5. 验证安装
python -c "from algebraic_structures import __version__; print(__version__)"
```

### 7.2 Docker部署

创建 `Dockerfile`:

```dockerfile
FROM python:3.10-slim

WORKDIR /app

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    gcc \
    g++ \
    && rm -rf /var/lib/apt/lists/*

# 复制依赖文件
COPY requirements.txt .

# 安装Python依赖
RUN pip install --no-cache-dir -r requirements.txt

# 复制项目文件
COPY . .

# 安装包
RUN pip install -e .

# 暴露端口（如果使用Web API）
EXPOSE 5000

# 运行应用
CMD ["python", "-m", "algebraic_structures.tools.api"]
```

构建和运行：

```bash
# 构建镜像
docker build -t algebraic-structures:latest .

# 运行容器
docker run -p 5000:5000 algebraic-structures:latest

# 或使用docker-compose
docker-compose up
```

创建 `docker-compose.yml`:

```yaml
version: '3.8'

services:
  algebraic-structures:
    build: .
    ports:
      - "5000:5000"
    volumes:
      - ./data:/app/data
    environment:
      - ALGEBRAIC_STRUCTURES_LOG_LEVEL=INFO
    restart: unless-stopped
```

### 7.3 云部署

#### Heroku部署

创建 `Procfile`:

```text
web: python -m algebraic_structures.tools.api
```

创建 `runtime.txt`:

```text
python-3.10.0
```

部署命令：

```bash
heroku create algebraic-structures-app
git push heroku main
heroku open
```

#### AWS Lambda部署

创建 `lambda_handler.py`:

```python
from algebraic_structures.tools.api import app

def lambda_handler(event, context):
    # Lambda处理逻辑
    return {
        'statusCode': 200,
        'body': 'Algebraic Structures API'
    }
```

使用Zappa部署：

```bash
pip install zappa
zappa init
zappa deploy production
```

## 8. 性能优化

### 8.1 编译优化

```bash
# 使用Cython编译关键模块
pip install cython
cythonize -i algebraic_structures/group_theory/groups.py

# 或使用Numba JIT编译
pip install numba
# 在代码中使用 @numba.jit 装饰器
```

### 8.2 缓存配置

```python
# 在代码中配置缓存
from functools import lru_cache

@lru_cache(maxsize=128)
def expensive_computation(x):
    # 计算
    pass
```

### 8.3 并行计算

```python
# 使用joblib进行并行计算
from joblib import Parallel, delayed

results = Parallel(n_jobs=4)(
    delayed(compute)(item) for item in items
)
```

## 9. 故障排除

### 9.1 常见问题

#### 问题1: 导入错误

**错误**: `ModuleNotFoundError: No module named 'algebraic_structures'`

**解决方案**:

```bash
# 确保在正确的虚拟环境中
source venv/bin/activate

# 重新安装包
pip install -e .
```

#### 问题2: NumPy版本冲突

**错误**: `numpy.core.multiarray failed to import`

**解决方案**:

```bash
# 重新安装NumPy
pip uninstall numpy
pip install numpy>=1.20.0
```

#### 问题3: 内存不足

**错误**: `MemoryError`

**解决方案**:

- 使用生成器而非列表
- 减少缓存大小
- 分批处理数据

### 9.2 调试技巧

```python
# 启用详细日志
import logging
logging.basicConfig(level=logging.DEBUG)

# 使用pdb调试
import pdb
pdb.set_trace()

# 性能分析
import cProfile
cProfile.run('your_function()')
```

## 10. 更新和维护

### 10.1 更新依赖

```bash
# 检查过时的包
pip list --outdated

# 更新所有包
pip install --upgrade -r requirements.txt

# 或使用pip-tools
pip install pip-tools
pip-compile --upgrade requirements.in
```

### 10.2 版本管理

```bash
# 使用git标签管理版本
git tag -a v1.0.0 -m "Version 1.0.0"
git push origin v1.0.0
```

## 11. 安全考虑

### 11.1 依赖安全

```bash
# 检查安全漏洞
pip install safety
safety check

# 或使用pip-audit
pip install pip-audit
pip-audit
```

### 11.2 代码安全

- 验证用户输入
- 使用参数化查询（如果使用数据库）
- 限制资源使用
- 定期更新依赖

## 12. 资源链接

- **完整指南**: `00-Python实现-代数结构完整指南.md`
- **快速参考**: `00-Python实现-代数结构快速参考.md`
- **示例项目**: `00-Python实现-代数结构示例项目.md`
- **API文档**: 运行 `sphinx-build docs/ docs/_build/`

## 13. 获取帮助

### 13.1 文档资源

- 查看完整指南文档
- 查看API参考文档
- 查看示例项目

### 13.2 社区支持

- GitHub Issues: 报告问题和建议
- 讨论区: 提问和讨论
- 邮件列表: 订阅更新

---

**版本**: 1.0
**最后更新**: 2025年1月
**维护者**: FormalMath项目组
