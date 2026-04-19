---
title: FormalMath 语义搜索系统 - 快速启动指南
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 语义搜索系统 - 快速启动指南

## 1. 安装依赖

```bash
cd FormalMath-Enhanced/api

# 安装基础依赖
pip install -r requirements.txt

# 安装语义搜索依赖
pip install -r requirements-search.txt
```

## 2. 启动服务

```bash
# 开发模式
python main.py

# 或使用uvicorn
uvicorn main:app --reload --host 0.0.0.0 --port 8000
```

## 3. 访问服务

- API文档: 
- 搜索界面: 
- 服务状态: 

## 4. 快速测试

### 4.1 索引测试文档

```bash
curl -X POST "" \
  -H "Content-Type: application/json" \
  -d '{
    "doc_id": "test_001",
    "content": "黎曼猜想是关于黎曼ζ函数零点分布的猜想。",
    "metadata": {"branch": "数论"}
  }'
```

### 4.2 执行搜索

```bash
curl -X POST "" \
  -H "Content-Type: application/json" \
  -d '{
    "query": "黎曼猜想",
    "search_type": "hybrid",
    "k": 5
  }'
```

### 4.3 公式搜索

```bash
curl -X POST "" \
  -H "Content-Type: application/json" \
  -d '{
    "latex": "\\\\frac{a+b}{c}",
    "k": 5
  }'
```

### 4.4 数学问答

```bash
curl -X POST "" \
  -H "Content-Type: application/json" \
  -d '{
    "question": "什么是黎曼猜想？"
  }'
```

## 5. 使用Python客户端

```python
import requests

# 索引文档
docs = [
    {"id": "doc1", "content": "费马大定理...", "metadata": {"type": "定理"}},
    {"id": "doc2", "content": "勾股定理...", "metadata": {"type": "定理"}},
]

requests.post("",
              json={"documents": docs})

# 搜索
response = requests.post("",
                        json={"query": "定理证明", "k": 10})
results = response.json()["data"]["results"]

# 问答
response = requests.post("",
                        json={"question": "什么是费马大定理？"})
answer = response.json()["data"]["answer"]
```

## 6. 功能特性

- ✅ 语义搜索（向量相似度）
- ✅ 关键词搜索（BM25）
- ✅ 混合搜索（语义+关键词）
- ✅ LaTeX公式搜索（结构匹配）
- ✅ 公式相似度比较
- ✅ 数学问答系统
- ✅ 多跳推理
- ✅ 搜索建议/自动补全
- ✅ Web前端界面

## 7. 系统架构

```
用户查询 → API路由 → 搜索服务 → 向量索引/关键词索引
                 ↓
            结果融合 → 重排序 → 返回答案
```

## 8. 故障排除

### 问题1: 模型下载失败

**解决**: 预下载sentence-transformers模型

```python
from sentence_transformers import SentenceTransformer
model = SentenceTransformer('all-MiniLM-L6-v2')
```

### 问题2: FAISS安装失败

**解决**: 使用conda安装

```bash
conda install faiss-cpu -c pytorch
```

### 问题3: 搜索结果为空

**解决**: 确保已索引文档

```bash
curl 
```

## 9. API端点列表

| 端点 | 方法 | 描述 |
|------|------|------|
| /api/v1/search/search | POST | 执行搜索 |
| /api/v1/search/index | POST | 索引文档 |
| /api/v1/search/index/batch | POST | 批量索引 |
| /api/v1/search/formula | POST | 公式搜索 |
| /api/v1/search/ask | POST | 数学问答 |
| /api/v1/search/stats | GET | 搜索统计 |
| /static/search.html | GET | 搜索界面 |

## 10. 性能优化建议

1. **批量索引**: 使用批量索引API而非逐个索引
2. **索引类型**: 大数据集使用HNSW索引
3. **缓存**: 启用Redis缓存
4. **压缩**: 启用响应压缩

---

更多信息请查看 `app/services/README-语义搜索.md`
