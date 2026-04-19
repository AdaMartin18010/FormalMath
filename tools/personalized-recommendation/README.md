---
title: 个性化学习路径推荐系统
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# 个性化学习路径推荐系统

基于全局依赖图的个性化学习路径推荐算法实现。

## 功能特性

- 🎯 **多策略推荐**: 最短路径、牢固基础、快速预览、平衡模式
- 👤 **用户画像**: 学习风格、时间偏好、目标设定
- 📊 **路径可视化**: 时间线、依赖图、进度仪表板
- 🔌 **开放API**: 完整的RESTful API接口
- 📈 **进度追踪**: 实时监测学习进度和掌握度

## 快速开始

### 安装依赖

```bash
pip install -r requirements.txt
```

### 运行演示

```bash
python main.py demo
```

### 运行测试

```bash
python main.py test
```

### 启动API服务

```bash
python main.py api --host 0.0.0.0 --port 8000
```

## 代码示例

### 基本使用

```python
from personalized_recommendation import (
    UserProfile, RecommendationEngine,
    PathStrategy, create_sample_graph
)

# 创建概念图
graph = create_sample_graph()

# 创建用户画像
user = UserProfile(name="张三", email="zhangsan@example.com")
user.time_preference.daily_hours = 2.5

# 设置已掌握概念
user.update_mastery("set_theory", 0.85)
user.update_mastery("functions", 0.75)

# 生成推荐
engine = RecommendationEngine(graph)
paths = engine.recommend(
    user_profile=user,
    strategy=PathStrategy.BALANCED,
    target_concepts=["algebraic_topology"]
)

# 打印结果
print(f"推荐路径: {paths[0].name}")
print(f"预计时间: {paths[0].total_estimated_hours:.1f}小时")
```

### 使用预设模板

```python
from personalized_recommendation import create_preset_profile

# 使用进阶学习者模板
user = create_preset_profile("advanced_learner", name="李四")
```

### 导出可视化

```python
from personalized_recommendation import DashboardRenderer

renderer = DashboardRenderer()
html = renderer.render_full_dashboard(user, paths[0], graph)

with open("dashboard.html", "w", encoding="utf-8") as f:
    f.write(html)
```

## API使用

### 创建用户

```python
from personalized_recommendation import UserProfileAPI

result = UserProfileAPI.create_user(
    name="张三",
    email="zhangsan@example.com",
    preset_type="advanced_learner"
)
user_id = result['data']['user_id']
```

### 生成推荐

```python
from personalized_recommendation import RecommendationAPI

result = RecommendationAPI.recommend_paths(
    user_id=user_id,
    strategy="balanced",
    num_alternatives=2
)
paths = result['data']['paths']
```

## 项目结构

```
personalized-recommendation/
├── README.md                 # 本文件
├── requirements.txt          # 依赖列表
├── main.py                   # 主入口和演示
├── __init__.py              # 包初始化
├── user_profile.py          # 用户画像模型
├── recommendation_engine.py # 推荐算法引擎
├── path_visualization.py    # 路径可视化组件
└── api.py                   # API接口
```

## 算法说明

### 最短学习路径 (Shortest Time)

- 最小化总学习时间
- 识别可并行学习的概念
- 适合时间紧迫的学习者

### 最牢固基础路径 (Solid Foundation)

- 深度优先策略
- 确保依赖充分掌握
- 适合追求深度理解

### 快速预览路径 (Quick Overview)

- 广度优先策略
- 先建立整体框架
- 适合快速入门

### 平衡路径 (Balanced)

- 综合优化多目标
- 考虑时间、难度、风格
- 默认推荐策略

## 详细文档

完整文档见: `docs/00-全局学习路径/02-个性化学习路径推荐.md`

## 许可证

MIT License - 详见项目根目录 LICENSE 文件
