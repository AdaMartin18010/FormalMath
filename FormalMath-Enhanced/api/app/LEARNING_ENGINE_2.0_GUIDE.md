# 个性化学习引擎2.0 使用指南

## 概述

个性化学习引擎2.0是一个全面升级的智能学习系统，整合了认知科学、机器学习和社会学习的最新研究成果。

## 核心模块

### 1. 认知模型增强 (ml/)

#### 1.1 DNC知识追踪 (dnc_knowledge_tracing.py)

- **Differentiable Neural Computer**架构实现高精度知识状态追踪
- 外部可寻址记忆机制
- 时序关联维护
- 注意力读写机制
- 多头知识追踪集成

#### 1.2 遗忘曲线建模 (forgetting_curve.py)

- 基于艾宾浩斯遗忘曲线改进
- 个性化遗忘率调整
- 间隔重复调度器
- 最优复习时间计算

#### 1.3 个体差异建模 (individual_differences.py)

- 学习风格档案（视觉/言语、序列/整体、主动/反思）
- 认知能力评估（工作记忆、处理速度、逻辑推理等）
- 个性特征分析（大五人格模型）
- 实时交互更新

### 2. 动态难度调整 (recommendation/)

#### 2.1 自适应难度管理 (adaptive_difficulty.py)

- 实时难度评估
- 学习区检测（挫折区/学习区/无聊区）
- 项目反应理论(IRT)支持
- 计算机自适应测试(CAT)

#### 2.2 内容推荐引擎 (content_recommender.py)

- 基于内容的推荐
- 协同过滤
- 知识感知推荐
- 混合推荐策略
- 多样性优化

#### 2.3 多目标优化 (multi_objective.py)

- NSGA-II风格的多目标遗传算法
- 时间效率vs掌握深度平衡
- 广度vs深度权衡
- 兴趣vs基础兼顾

### 3. 社交学习 (social/)

#### 3.1 同伴匹配 (peer_matching.py)

- 多维度相似性匹配
- 知识互补性评估
- 时间安排匹配
- 学习风格兼容性

#### 3.2 小组推荐 (group_recommendation.py)

- 智能小组组建
- 多样性优化
- 小组健康度分析

#### 3.3 竞赛系统 (competition_system.py)

- 多种竞赛类型（个人/团队/限时/马拉松）
- 排行榜系统
- 游戏化引擎集成

### 4. 游戏化设计 (gamification/)

#### 4.1 徽章系统 (badges.py)

- 多层级徽章（铜/银/金/白金/钻石/特殊）
- 徽章系列收集
- 稀有度统计

#### 4.2 挑战系统 (challenges.py)

- 日常挑战
- 周挑战
- 特殊挑战
- 社区挑战

#### 4.3 进度可视化 (progress_visualization.py)

- 里程碑管理
- 学习热力图
- 技能树可视化
- 进度报告生成

## API使用示例

### 初始化用户

```python
import requests

# 初始化用户
response = requests.post("/api/v1/learning-engine/users/initialize", json={
    "user_id": "user_123",
    "initial_assessment": {
        "learning_style": {
            "visual_verbal": 0.3,
            "sequential_global": -0.2
        },
        "knowledge_levels": {
            "calculus_basic": 0.7,
            "linear_algebra": 0.5
        }
    }
})
```

### 记录学习交互

```python
response = requests.post("/api/v1/learning-engine/interactions/record", json={
    "user_id": "user_123",
    "concept_id": "derivative_rules",
    "interaction_type": "exercise",
    "result": {
        "correctness": "correct",
        "time_spent": 120,
        "difficulty": 0.6,
        "score": 95
    }
})
```

### 获取学习推荐

```python
response = requests.post("/api/v1/learning-engine/recommendations/session", json={
    "user_id": "user_123",
    "session_duration": 30,
    "target_concepts": ["chain_rule", "product_rule"]
})
```

### 获取间隔重复计划

```python
response = requests.get("/api/v1/learning-engine/users/user_123/spaced-repetition?days_ahead=7")
```

### 寻找学习伙伴

```python
response = requests.post("/api/v1/learning-engine/social/peers/match", json={
    "user_id": "user_123",
    "purpose": "study",
    "top_k": 5
})
```

### 获取游戏化摘要

```python
response = requests.get("/api/v1/learning-engine/gamification/user_123/summary")
```

## 系统架构

```
┌─────────────────────────────────────────────────────────────┐
│                    个性化学习引擎2.0                          │
├─────────────────────────────────────────────────────────────┤
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ DNC知识追踪   │  │ 遗忘曲线模型  │  │ 个体差异模型  │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
├─────────────────────────────────────────────────────────────┤
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ 动态难度调整  │  │ 内容推荐引擎  │  │ 多目标优化   │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
├─────────────────────────────────────────────────────────────┤
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ 同伴匹配     │  │ 小组推荐     │  │ 竞赛系统     │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
├─────────────────────────────────────────────────────────────┤
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ 徽章系统     │  │ 挑战系统     │  │ 进度可视化   │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
└─────────────────────────────────────────────────────────────┘
```

## 核心特性

### 智能认知建模

- 使用DNC架构实现高精度知识追踪
- 基于遗忘曲线的智能复习调度
- 多维度个体差异建模

### 个性化推荐

- 自适应难度调整
- 多策略内容推荐
- 多目标优化路径规划

### 社交学习

- 智能同伴匹配
- 最优小组组建
- 竞赛激励机制

### 游戏化设计

- 丰富的徽章系统
- 多样化挑战任务
- 直观的进度可视化

## 技术亮点

1. **Differentiable Neural Computer (DNC)**
   - 外部可寻址记忆
   - 时序关联维护
   - 注意力读写机制

2. **多目标遗传算法**
   - NSGA-II风格优化
   - Pareto前沿求解
   - 用户偏好平衡

3. **项目反应理论(IRT)**
   - 2PL/3PL模型支持
   - 自适应测试
   - 精确能力估计

4. **实时个性化**
   - 增量模型更新
   - 流式数据处理
   - 低延迟响应

## 部署说明

### 依赖安装

```bash
pip install numpy scipy scikit-learn
```

### 服务启动

```bash
uvicorn app.main:app --reload
```

### 配置环境变量

```env
REDIS_URL=redis://localhost:6379/0
DATABASE_URL=postgresql://user:pass@localhost/db
```

## 开发计划

- [ ] 深度强化学习推荐
- [ ] 联邦学习支持
- [ ] 多模态学习分析
- [ ] 实时协作功能

## 贡献指南

欢迎提交Issue和PR！

## 许可证

MIT License
