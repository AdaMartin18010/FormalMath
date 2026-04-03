---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# AI形式化数学工具使用说明

## 工具概览

本目录包含5个核心工具模块，用于数学问题的自动形式化。

## 工具列表

### 1. deepseek_client.py - DeepSeek API客户端
功能：调用DeepSeek-Math API进行数学推理和形式化转换

```python
from deepseek_client import DeepSeekClient, FormalizationMode

# 初始化客户端
client = DeepSeekClient()

# 形式化数学问题
result = client.formalize(
    "证明：对于任意正整数n，n³ - n能被6整除。",
    mode=FormalizationMode.NATURAL_TO_LEAN
)

if result.success:
    print(result.content)  # Lean 4代码
```

### 2. lean_verifier.py - Lean4验证器
功能：验证Lean4代码语法和类型

```python
from lean_verifier import LeanVerifier

verifier = LeanVerifier()
result = verifier.verify("""
import Mathlib

theorem test (n : ℕ) : n + 0 = n := by
    simp
""")

print(f"Valid: {result.is_valid}")
print(f"Errors: {len(result.errors)}")
```

### 3. imo_dataset.py - IMO数据集处理器
功能：读取和处理IMO竞赛题目

```python
from imo_dataset import IMODatasetProcessor

processor = IMODatasetProcessor()
problems = processor.load_problems()

# 搜索题目
results = processor.search_problems("prime")

# 导出数据集
processor.export_to_json("imo_problems.json")
```

### 4. msc_recommender.py - MSC编码推荐器
功能：为数学文本推荐MSC2020编码

```python
from msc_recommender import MSCRecommender

recommender = MSCRecommender()
recommendations = recommender.recommend(
    "Prove that for any prime p...",
    top_k=3
)

for rec in recommendations:
    print(f"{rec.code}: {rec.description} (confidence: {rec.confidence})")
```

### 5. auto_formalize.py - 自动化工作流
功能：整合所有工具的端到端形式化流程

```python
from auto_formalize import AutoFormalizationWorkflow

workflow = AutoFormalizationWorkflow()
task = workflow.process_problem("证明勾股定理...")

print(task.generated_lean_code)
print(task.verification_result.is_valid)
```

## 环境变量配置

```bash
# DeepSeek API
export DEEPSEEK_API_KEY="your-api-key"
export DEEPSEEK_BASE_URL="https://api.deepseek.com/v1"
export DEEPSEEK_MODEL="deepseek-math"

# Lean环境
export LEAN_PROJECT_PATH="/path/to/lean/project"
export LEAN_TIMEOUT="60"

# IMO数据
export IMO_DATA_PATH="../../03-IMO-Competition"
```

## 运行示例

### 命令行运行

```bash
# 交互式模式
cd tools
python auto_formalize.py

# 单独使用某个工具
python deepseek_client.py
python lean_verifier.py
python imo_dataset.py
python msc_recommender.py
```

### Jupyter Notebook

```bash
cd examples
jupyter notebook usage_examples.ipynb
```

### Docker运行

```bash
# 构建镜像
cd ..
docker build -t formalmath-ai .

# 运行容器
docker run -it \
  -e DEEPSEEK_API_KEY=$DEEPSEEK_API_KEY \
  -p 8888:8888 \
  -v $(pwd):/workspace \
  formalmath-ai

# 在容器内启动Jupyter
jupyter lab --ip=0.0.0.0 --port=8888 --no-browser --allow-root
```

## 依赖安装

```bash
pip install -r ../requirements.txt
```

## 快速开始

```python
# 最简使用示例
from auto_formalize import quick_formalize

result = quick_formalize("证明：对任意正整数n，n²是偶数则n也是偶数。")

if result["success"]:
    print(result["lean_code"])
    print(result["msc_codes"])
```
