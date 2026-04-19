---
title: 推荐系统 v2.0
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# 推荐系统 v2.0

## 概述

这是FormalMath平台的高级混合推荐系统，整合了多种推荐算法和优化策略，旨在提供准确、多样且可解释的个性化学习推荐。

## 核心功能

### 1. 动态权重调整 (Dynamic Weight Adjustment)

基于用户反馈实时调整各推荐器的权重，使用动量梯度下降优化算法。

```python
from app.recommendation import DynamicWeightAdjuster

# 创建权重调整器
adjuster = DynamicWeightAdjuster(
    learning_rate=0.05,
    min_weight=0.05,
    max_weight=0.6,
    momentum=0.9
)

# 记录反馈
adjuster.record_feedback(feedback, component_contributions)

# 获取优化后的权重
weights = adjuster.get_weights(user_id=123)
```

### 2. 反馈学习机制 (Feedback Learning)

多维度用户反馈收集与在线学习系统，支持多种用户行为类型。

**支持的反馈动作:**
- `click` - 点击推荐
- `complete` - 完成学习
- `bookmark` - 收藏
- `share` - 分享
- `dismiss` - 忽略
- `skip` - 跳过
- `rate` - 评分

### 3. 冷启动优化 (Cold Start Handling)

多层次的冷启动处理策略，针对不同新用户类型提供个性化推荐。

| 等级 | 描述 | 策略 |
|------|------|------|
| NEW_USER | 完全新用户 | 热门基础概念 + 多领域探索 |
| INTEREST_KNOWN | 已知兴趣 | 兴趣匹配 + 个性化入门 |
| SOME_ACTIVITY | 有一些活动 | 学习延续 + 适度探索 |
| WARM_USER | 接近正常用户 | 标准推荐算法 |

### 4. 多样性算法 (Diversity Enhancement)

基于MMR (Maximal Marginal Relevance) 算法的多样性增强，确保推荐结果的多样性。

**多样性指标:**
- Intra-list Diversity: 列表内多样性
- Inter-list Diversity: 列表间多样性
- Branch Coverage: 分支覆盖率
- Shannon Entropy: 香农熵

### 5. 可解释性输出 (Explainability)

详细的推荐理由和透明度报告，帮助用户理解推荐逻辑。

**解释内容:**
- Primary Reason: 主要推荐理由
- Contributing Factors: 贡献因素
- Algorithm Breakdown: 算法贡献分解
- User Profile Match: 用户画像匹配度
- Confidence Explanation: 置信度解释

## 快速开始

### 基本使用

```python
from app.recommendation import get_advanced_recommender

# 创建推荐器
db = get_db_session()
recommender = get_advanced_recommender(db)
recommender.initialize()

# 生成推荐
result = recommender.recommend(
    user_id=123,
    n_recommendations=10,
    enable_diversity=True,
    enable_explanation=True
)

# 处理结果
for rec in result["recommendations"]:
    print(f"{rec['name']}: {rec['final_score']:.4f}")
    print(f"  理由: {rec['explanation']['primary_reason']}")
```

### 记录用户反馈

```python
# 记录用户点击
recommender.record_feedback(
    user_id=123,
    concept_id="algebra_group_theory",
    action="click"
)

# 记录用户完成学习并评分
recommender.record_feedback(
    user_id=123,
    concept_id="algebra_group_theory",
    action="complete",
    rating=4.5
)
```

## A/B测试

### 使用预设模板

```python
from app.recommendation import get_ab_testing_manager

manager = get_ab_testing_manager()

# 创建测试
test = manager.create_test_from_template(
    template_name="weight_optimization",
    test_id="weight_test_001"
)

# 启动测试
manager.start_test(test.test_id)

# 分配用户
variant = manager.assign_user_to_variant(test.test_id, user_id=123)

# 记录事件
manager.record_event(
    test_id=test.test_id,
    user_id=123,
    event_type="click",
    value=1.0
)

# 获取结果
results = manager.get_test_results(test.test_id)
```

### 可用测试模板

| 模板名称 | 描述 |
|---------|------|
| weight_optimization | 推荐器权重优化测试 |
| diversity_algorithm | 多样性算法效果测试 |
| cold_start_strategy | 冷启动策略对比 |
| explanation_effectiveness | 解释性推荐效果测试 |
| feedback_learning | 反馈学习机制测试 |

## 性能评估

### 生成评估报告

```python
from app.recommendation import create_evaluation_report

# 生成完整报告
report_path = create_evaluation_report(
    recommender=recommender,
    test_users=[1, 2, 3, ...],
    db_session=db,
    output_dir="./reports"
)
```

### 评估维度

1. **准确性 (Accuracy)**
   - Precision@K
   - Recall@K
   - NDCG@K
   - MRR
   - MAP

2. **多样性 (Diversity)**
   - Intra-list Diversity
   - Inter-list Diversity
   - Branch Coverage
   - Shannon Entropy

3. **覆盖率 (Coverage)**
   - Catalog Coverage
   - User Coverage
   - Long-tail Coverage

4. **用户满意度 (Satisfaction)**
   - Click Through Rate
   - Conversion Rate
   - Average Rating
   - User Engagement

5. **系统性能 (Performance)**
   - Response Time
   - Throughput
   - Error Rate

6. **冷启动 (Cold Start)**
   - New User CTR
   - Time to First Engagement
   - Early Retention

## 系统架构

```
AdvancedHybridRecommender
├── DynamicWeightAdjuster      # 动态权重调整
├── DiversityEnhancer          # 多样性增强
├── ColdStartHandler           # 冷启动处理
├── ExplainabilityEngine       # 可解释性引擎
└── Base Recommenders          # 基础推荐器
    ├── CollaborativeFiltering # 协同过滤
    ├── KnowledgeGraphEmbedding # 知识图谱
    ├── RLRecommender          # 强化学习
    └── ContentRecommender     # 内容推荐
```

## 配置文件

### 推荐系统配置示例

```python
RECOMMENDATION_CONFIG = {
    "dynamic_weights": {
        "learning_rate": 0.05,
        "min_weight": 0.05,
        "max_weight": 0.6,
        "momentum": 0.9,
        "regularization": 0.01
    },
    "diversity": {
        "lambda_param": 0.5,
        "branch_diversity_weight": 0.4,
        "difficulty_diversity_weight": 0.3,
        "novelty_weight": 0.3
    },
    "cold_start": {
        "popular_items_count": 10,
        "exploration_ratio": 0.3
    },
    "explanation": {
        "include_alternatives": True,
        "detail_level": "detailed"
    }
}
```

## 性能优化建议

1. **缓存策略**: 对热门推荐结果进行缓存
2. **批量处理**: 使用批处理收集和处理用户反馈
3. **异步更新**: 权重更新和模型训练异步执行
4. **增量计算**: 使用增量方式计算用户相似度

## 版本历史

### v2.0.0 (2024-04)
- 新增动态权重调整
- 新增反馈学习机制
- 新增多样性算法
- 新增冷启动优化
- 新增可解释性输出
- 新增A/B测试框架
- 新增性能评估报告

### v1.x (之前版本)
- 基础混合推荐
- 协同过滤
- 知识图谱嵌入
- 强化学习推荐

## 贡献指南

欢迎提交Issue和PR来改进推荐系统。

## 许可证

MIT License
