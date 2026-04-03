---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# FormalMath 自适应学习路径系统

T3.1 自适应学习路径系统的完整实现，基于 FastAPI + React + 知识图谱。

## 功能特性

### 后端功能

- **学习路径引擎**
  - 学习者特征分析（认知风格、先验知识、学习偏好）
  - 路径生成算法（A*算法、动态规划）
  - 实时调整机制（根据学习表现动态调整路径）
  - 学习支持系统（资源推荐、难度调节）

- **知识图谱数据**
  - 数学概念节点模型
  - 概念间关系模型（先修、后继、相关）
  - 知识图谱构建与查询
  - 与FormalMath项目现有知识图谱对接

- **路径规划算法**
  - A* 算法：最短路径优先，考虑先修知识、难度匹配、兴趣相关
  - 动态规划：多目标优化，平衡学习时间、掌握度、体验
  - 强化学习：智能探索（预留接口）

### 前端功能

- **路径可视化**
  - 学习路径图（概念节点+连接线）
  - 进度追踪界面
  - 资源推荐展示
  - 学习日历/计划视图

- **交互组件**
  - 概念掌握度标记
  - 路径调整确认对话框
  - 学习反馈收集

## 项目结构

```
adaptive-learning/
├── backend/
│   ├── app/
│   │   ├── api/
│   │   │   ├── __init__.py
│   │   │   └── adaptive_routes.py       # API端点
│   │   ├── adaptive/
│   │   │   ├── __init__.py
│   │   │   ├── learner_profiler.py      # 学习者画像分析
│   │   │   ├── path_generator.py        # 路径生成算法
│   │   │   ├── path_adjuster.py         # 路径调整
│   │   │   └── resource_recommender.py  # 资源推荐
│   │   ├── knowledge_graph/
│   │   │   ├── __init__.py
│   │   │   └── graph_builder.py         # 知识图谱构建
│   │   ├── schemas/
│   │   │   ├── __init__.py
│   │   │   └── models.py                # Pydantic模型
│   │   ├── core/
│   │   │   ├── __init__.py
│   │   │   └── config.py                # 配置文件
│   │   ├── main.py                      # FastAPI主应用
│   │   └── __init__.py
│   ├── requirements.txt
│   └── .env.example
│
└── frontend/
    ├── src/
    │   ├── api/
    │   │   ├── client.ts                  # HTTP客户端
    │   │   └── adaptiveApi.ts             # API接口
    │   ├── components/
    │   │   └── Adaptive/
    │   │       ├── PathVisualization.tsx  # 路径可视化
    │   │       ├── ProgressTracker.tsx    # 进度追踪
    │   │       ├── ResourceList.tsx       # 资源列表
    │   │       ├── ConceptCard.tsx        # 概念卡片
    │   │       └── PathGenerator.tsx      # 路径生成器
    │   ├── pages/
    │   │   ├── Home.tsx                   # 首页
    │   │   ├── Paths.tsx                  # 路径管理
    │   │   ├── CreatePath.tsx             # 创建路径
    │   │   └── Explore.tsx                # 知识图谱探索
    │   ├── types/
    │   │   └── index.ts                   # TypeScript类型
    │   ├── App.tsx                        # 主应用
    │   └── main.tsx                       # 入口文件
    ├── package.json
    ├── tsconfig.json
    └── vite.config.ts
```

## 快速开始

### 后端启动

```bash
cd backend

# 创建虚拟环境
python -m venv venv
source venv/bin/activate  # Windows: venv\Scripts\activate

# 安装依赖
pip install -r requirements.txt

# 启动服务
uvicorn app.main:app --reload
```

后端服务将在 http://localhost:8000 启动

API文档: http://localhost:8000/docs

### 前端启动

```bash
cd frontend

# 安装依赖
npm install

# 启动开发服务器
npm run dev
```

前端服务将在 http://localhost:3000 启动

## API 端点

| 方法 | 端点 | 描述 |
|------|------|------|
| POST | /api/adaptive/path | 生成学习路径 |
| GET | /api/adaptive/path/{user_id} | 获取用户路径列表 |
| GET | /api/adaptive/path/detail/{path_id} | 获取路径详情 |
| POST | /api/adaptive/adjust | 调整学习路径 |
| GET | /api/adaptive/recommendations/{user_id} | 获取资源推荐 |
| POST | /api/adaptive/progress/update | 更新学习进度 |
| POST | /api/adaptive/mastery/update | 更新概念掌握度 |
| GET | /api/adaptive/suggest/{user_id} | 获取下一步建议 |
| GET | /api/adaptive/concepts/search | 搜索概念 |
| GET | /api/adaptive/concepts/{concept_id} | 获取概念详情 |
| GET | /api/adaptive/stats/{user_id} | 获取用户统计 |

## 路径生成算法说明

### A* 算法

1. **启发函数**: 使用到目标的先修概念数量差作为启发
2. **代价函数**: 综合考虑先修知识缺口、难度匹配、兴趣相关、学习连续性
3. **搜索策略**: 优先扩展 f = g + h 值最小的节点

### 动态规划

1. **状态定义**: dp[i] 表示学习到第 i 个概念的最优状态
2. **状态转移**: 基于先修关系和综合评分进行转移
3. **优化目标**: 最小化时间、最大化掌握度、优化学习体验

## 配置说明

### 环境变量

| 变量名 | 描述 | 默认值 |
|--------|------|--------|
| DEBUG | 调试模式 | True |
| DATABASE_URL | 数据库连接 | sqlite:///./adaptive_learning.db |
| DEFAULT_ALGORITHM | 默认路径算法 | astar |
| MASTERY_THRESHOLD | 掌握度阈值 | 0.8 |
| STRUGGLE_THRESHOLD | 困难阈值 | 0.4 |

## 技术栈

- **后端**: Python 3.8+, FastAPI, NetworkX, Pydantic
- **前端**: React 18, TypeScript, Ant Design, D3.js
- **知识图谱**: NetworkX (图算法), YAML (数据源)

## 与 FormalMath 项目的集成

系统直接读取 `project/links/cross-branch-links.yaml` 作为知识图谱数据源，与 FormalMath 主项目的概念体系保持一致。
