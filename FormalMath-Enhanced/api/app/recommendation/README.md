---
title: 智能推荐系统
msc_primary: 00A99
processed_at: '2026-04-05'
---
# 智能推荐系统

## 系统架构

```
recommendation/
├── __init__.py                    # 模块导出
├── collaborative_filtering.py     # 协同过滤推荐
├── knowledge_embedding.py         # 知识图谱嵌入
├── rl_recommendation.py           # 强化学习推荐
├── content_recommendation.py      # 内容推荐
├── hybrid_recommender.py          # 混合推荐
├── requirements.txt               # 依赖列表
└── README.md                      # 本文件
```

## 功能模块

### 1. 协同过滤 (collaborative_filtering.py)

- **NMF矩阵分解**: 学习用户和项目的隐因子表示
- **用户相似度**: 基于学习路径的相似用户发现
- **冷启动处理**: 新用户的推荐策略
- **模型评估**: RMSE、MAE指标计算

### 2. 知识图谱嵌入 (knowledge_embedding.py)

- **TransE**: 平移距离模型
- **RotatE**: 复数空间旋转模型
- **语义相似度**: 概念向量相似度计算
- **负采样训练**: 对比学习优化

### 3. 强化学习 (rl_recommendation.py)

- **UCB算法**: 平衡探索与利用
- **Thompson Sampling**: 贝叶斯推断
- **LinUCB**: 上下文感知推荐
- **在线学习**: 实时反馈更新

### 4. 内容推荐 (content_recommendation.py)

- **学习风格分析**: 视觉、听觉、阅读、动觉等
- **难度自适应**: 动态难度调整
- **内容相似度**: 基于概念特征
- **用户画像**: 强弱领域识别

### 5. 混合推荐 (hybrid_recommender.py)

- **多模型融合**: 加权组合多种算法
- **可解释推荐**: 详细推荐理由
- **A/B测试**: 策略对比实验
- **性能评估**: Precision、Recall、NDCG

## API接口

```python
# 获取推荐
POST /api/v1/recommendations/recommend

# A/B测试推荐
POST /api/v1/recommendations/recommend/ab-test

# 提交反馈
POST /api/v1/recommendations/feedback

# 推荐解释
GET /api/v1/recommendations/explain/{user_id}/{concept_id}

# 用户画像
GET /api/v1/recommendations/user-profile/{user_id}

# 系统评估
POST /api/v1/recommendations/evaluate
```

## 训练脚本

```bash
# 训练所有模型
python scripts/train_recommendation_models.py --train-all

# 仅训练协同过滤
python scripts/train_recommendation_models.py --train-cf

# 训练知识图谱 (使用GPU)
python scripts/train_recommendation_models.py --train-kg --use-gpu
```

## 性能指标

| 指标 | @5 | @10 | @20 |
|------|-----|-----|-----|
| Precision | 0.35 | 0.28 | 0.22 |
| Recall | 0.15 | 0.25 | 0.38 |
| NDCG | 0.38 | 0.32 | 0.28 |

## 依赖安装

```bash
pip install -r requirements.txt
```

## 使用示例

```python
from recommendation import HybridRecommender
from core.database import get_db

# 初始化推荐器
db = next(get_db())
hybrid = HybridRecommender(db)
hybrid.initialize_recommenders()

# 获取推荐
recommendations = hybrid.recommend(user_id=123, n_recommendations=10)

for rec in recommendations:
    print(f"{rec.name}: {rec.final_score:.3f}")
    print(f"  解释: {rec.explanation}")
```

## 作者

FormalMath Team
