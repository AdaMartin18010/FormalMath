---
title: FormalMath 语义搜索系统
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 语义搜索系统

## 系统架构

```
┌─────────────────────────────────────────────────────────────┐
│                     语义搜索服务层                            │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
│  │  混合搜索    │  │  公式搜索    │  │     问答系统         │  │
│  │  (Hybrid)   │  │  (Formula)  │  │      (QA)           │  │
│  └──────┬──────┘  └──────┬──────┘  └──────────┬──────────┘  │
│         └─────────────────┼────────────────────┘             │
│                           │                                  │
│  ┌────────────────────────┼────────────────────────┐        │
│  │                   核心服务层                       │        │
│  │  ┌─────────────┐  ┌─────────────┐  ┌──────────┐ │        │
│  │  │   嵌入服务   │  │  向量存储    │  │  重排序   │ │        │
│  │  │(Embedding)  │  │ (VectorStore)│  │(Reranker)│ │        │
│  │  └─────────────┘  └─────────────┘  └──────────┘ │        │
│  └──────────────────────────────────────────────────┘        │
└─────────────────────────────────────────────────────────────┘
```

## 核心模块

### 1. 嵌入服务 (`embedding.py`)

**LaTeXTokenizer** - LaTeX感知分词器
- 提取文本中的数学公式
- 标准化LaTeX表达式
- 分离文本和公式内容

**FormulaEmbedder** - 公式嵌入器
- 生成公式的结构哈希
- 提取结构特征（操作符、函数、变量）
- 变量无关的结构相似度计算

**EmbeddingService** - 嵌入服务
- 文本向量化（支持sentence-transformers）
- 数学内容嵌入（LaTeX感知）
- 余弦相似度计算

### 2. 向量存储 (`vector_store.py`)

**VectorStore** - 向量存储
- FAISS索引（精确/近似搜索）
- Fallback索引（线性搜索）
- 元数据过滤
- 持久化支持

### 3. 混合搜索 (`hybrid_search.py`)

**HybridSearchService** - 混合搜索服务
- 语义搜索（向量相似度）
- 关键词搜索（BM25）
- 结果融合与重排序
- RRF（Reciprocal Rank Fusion）

### 4. 公式搜索 (`formula_search.py`)

**FormulaSearchService** - 公式搜索服务
- LaTeX结构匹配
- 变量无关匹配
- 结构相似度计算
- 公式提取与索引

### 5. 问答系统 (`qa_system.py`)

**QASystem** - 问答系统
- 问题分析（意图识别、实体提取）
- 答案抽取
- 多跳推理
- 上下文理解

## API端点

### 搜索相关

```
POST /api/v1/search/search          - 执行搜索
GET  /api/v1/search/search?q=...    - GET方式搜索
POST /api/v1/search/index           - 索引文档
POST /api/v1/search/index/batch     - 批量索引
DELETE /api/v1/search/index/{id}    - 删除文档
```

### 公式搜索

```
POST /api/v1/search/formula         - 公式搜索
POST /api/v1/search/formula/compare - 比较公式
```

### 问答系统

```
POST /api/v1/search/ask             - 数学问答
POST /api/v1/search/suggest-questions - 获取建议问题
```

### 其他

```
GET /api/v1/search/stats            - 搜索统计
GET /api/v1/search/suggest?q=...    - 搜索建议
POST /api/v1/search/save            - 保存索引
```

## 使用示例

### 1. 搜索文档

```python
import requests

# 执行搜索
response = requests.post("", json={
    "query": "黎曼猜想",
    "search_type": "hybrid",
    "k": 10,
    "rerank": True
})

results = response.json()["data"]["results"]
```

### 2. 索引文档

```python
# 索引单个文档
response = requests.post("", json={
    "doc_id": "math_001",
    "content": "黎曼猜想是关于黎曼ζ函数零点分布的猜想...",
    "metadata": {
        "branch": "数论",
        "difficulty": "advanced",
        "tags": ["猜想", "素数"]
    }
})
```

### 3. 公式搜索

```python
# 搜索相似公式
response = requests.post("", json={
    "latex": "\\frac{a+b}{c}",
    "k": 10,
    "match_type": "all"
})

formulas = response.json()["data"]["results"]
```

### 4. 数学问答

```python
# 提问
response = requests.post("", json={
    "question": "什么是黎曼猜想？",
    "use_multi_hop": True
})

answer = response.json()["data"]["answer"]
```

## 前端界面

访问 `/static/search.html` 使用搜索前端界面，支持：
- 混合搜索
- 智能问答
- 公式搜索
- 自动补全

## 依赖安装

```bash
# 安装语义搜索依赖
pip install -r requirements-search.txt

# 或使用conda
conda install faiss-cpu -c pytorch
pip install sentence-transformers
```

## 配置选项

```python
# embedding.py
EmbeddingConfig(
    model_name="sentence-transformers/all-MiniLM-L6-v2",
    dimension=384,
    latex_weight=1.5,      # 公式权重
    text_weight=1.0,       # 文本权重
    normalize=True
)

# vector_store.py
VectorStore(
    collection_name="default",
    dimension=384,
    index_type="Flat"      # Flat, IVF, HNSW, PQ
)

# hybrid_search.py
HybridSearchService(
    alpha=0.6              # 语义搜索权重
)
```

## 性能优化

1. **索引选择**
   - 小数据集（<10K）：使用Flat索引
   - 中数据集（10K-1M）：使用IVF索引
   - 大数据集（>1M）：使用HNSW索引

2. **批量操作**
   - 使用批量索引提高性能
   - 批量搜索减少API调用

3. **缓存**
   - 嵌入结果缓存
   - 搜索结果缓存

## 注意事项

1. **模型加载**
   - 首次启动时会下载embedding模型
   - 需要网络连接或预下载模型

2. **内存使用**
   - FAISS索引会占用内存
   - 大数据集考虑使用磁盘索引

3. **LaTeX解析**
   - 使用正则表达式提取公式
   - 复杂嵌套结构可能无法完全解析
