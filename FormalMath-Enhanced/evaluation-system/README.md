---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: FormalMath T2.2 评估系统
---
# FormalMath T2.2 评估系统

基于五维评估模型的完整评估系统，包含过程性评价、增值评价、表现性评价和发散思维评价。

## 目录结构

```
FormalMath-Enhanced/evaluation-system/
├── backend/                    # FastAPI 后端
│   ├── app/
│   │   ├── api/               # API 路由
│   │   │   ├── __init__.py
│   │   │   ├── evaluation.py  # 评估API端点
│   │   │   └── schemas.py     # Pydantic模型
│   │   ├── core/              # 核心配置
│   │   │   ├── __init__.py
│   │   │   ├── config.py      # 应用配置
│   │   │   └── database.py    # 数据库配置
│   │   ├── evaluation/        # 评估引擎
│   │   │   ├── __init__.py
│   │   │   ├── model.py       # 五维评估模型
│   │   │   ├── engine.py      # 评估引擎
│   │   │   ├── feedback.py    # 反馈生成引擎
│   │   │   └── report.py      # 报告生成器
│   │   ├── models/            # 数据库模型
│   │   │   ├── __init__.py
│   │   │   └── evaluation.py  # 评估相关模型
│   │   └── __init__.py
│   ├── tests/                 # 测试文件
│   │   ├── __init__.py
│   │   └── test_evaluation.py
│   ├── main.py                # 应用入口
│   └── requirements.txt       # 依赖
│
└── frontend/                   # React + TypeScript 前端
    ├── public/
    │   └── index.html
    ├── src/
    │   ├── api/               # API客户端
    │   │   ├── client.ts
    │   │   └── evaluation.ts
    │   ├── components/        # 组件
    │   │   └── Evaluation/
    │   │       ├── RadarChart.tsx
    │   │       ├── GrowthCurve.tsx
    │   │       ├── ScoreInput.tsx
    │   │       ├── ReportDisplay.tsx
    │   │       └── index.ts
    │   ├── pages/             # 页面
    │   │   ├── AssessmentPage.tsx
    │   │   ├── ReportPage.tsx
    │   │   ├── ProgressPage.tsx
    │   │   ├── FeedbackPage.tsx
    │   │   └── index.ts
    │   ├── types/             # TypeScript类型
    │   │   └── index.ts
    │   ├── App.tsx
    │   ├── App.css
    │   └── index.tsx
    ├── package.json
    └── tsconfig.json
```

## 五维评估模型

| 维度 | 名称 | 权重 | 描述 |
|------|------|------|------|
| knowledge_mastery | 知识掌握度 | 30% | 对数学概念、定理、公式的理解和掌握程度 |
| problem_solving | 问题解决能力 | 25% | 分析问题、制定策略、解决问题的能力 |
| proof_ability | 证明能力 | 20% | 数学证明的逻辑性、严谨性和创造性 |
| application | 应用能力 | 15% | 将数学知识应用于实际问题的能力 |
| innovation | 创新思维 | 10% | 创造性思维、发散思维和探索精神 |

## API 端点

### 评估管理
- `POST /api/evaluation/assess` - 执行评估
- `GET /api/evaluation/report/{user_id}` - 获取评估报告
- `GET /api/evaluation/progress/{user_id}` - 获取学习轨迹
- `POST /api/evaluation/feedback` - 生成反馈

### 数据查询
- `GET /api/evaluation/records/{user_id}` - 获取用户评估记录
- `GET /api/evaluation/statistics/{user_id}` - 获取用户统计信息
- `GET /api/evaluation/dimensions` - 获取评估维度信息

### 标准管理
- `GET /api/evaluation/standards` - 列评估标准
- `POST /api/evaluation/standards` - 创建评估标准

### 系统
- `GET /` - 系统信息
- `GET /health` - 健康检查
- `GET /api/docs` - API文档 (Swagger UI)

## 运行说明

### 后端运行

```bash
# 进入后端目录
cd FormalMath-Enhanced/evaluation-system/backend

# 创建虚拟环境
python -m venv venv

# 激活虚拟环境
# Windows:
venv\Scripts\activate
# macOS/Linux:
source venv/bin/activate

# 安装依赖
pip install -r requirements.txt

# 运行开发服务器
uvicorn main:app --reload --host 0.0.0.0 --port 8000

# 访问 API 文档
# 
```

### 前端运行

```bash
# 进入前端目录
cd FormalMath-Enhanced/evaluation-system/frontend

# 安装依赖 (使用npm或yarn)
npm install
# 或
yarn install

# 启动开发服务器
npm start
# 或
yarn start

# 访问应用
# 
```

## 功能特性

### 评估引擎
- 五维加权评分算法
- 成长曲线计算
- 班级对比分析
- 优势/弱点识别

### 反馈系统
- 个性化反馈生成
- 学习建议推荐
- 学习路径规划
- 资源推荐

### 可视化
- 五维雷达图 (Recharts)
- 学习曲线图
- 对比分析图
- 分数分布统计

### 报告生成
- JSON格式报告
- PDF格式报告 (可选)
- 执行摘要
- 详细分析

## 代码行数统计

| 模块 | 文件数 | 代码行数 |
|------|--------|----------|
| 后端 API | 3 | ~600 |
| 后端引擎 | 4 | ~1,200 |
| 后端模型 | 2 | ~300 |
| 后端配置 | 3 | ~200 |
| 后端测试 | 1 | ~400 |
| 前端 API | 2 | ~150 |
| 前端组件 | 4 | ~800 |
| 前端页面 | 4 | ~1,200 |
| 前端类型 | 1 | ~250 |
| **总计** | **24** | **~5,100** |

## 技术栈

### 后端
- Python 3.9+
- FastAPI
- SQLAlchemy
- SQLite (可扩展至PostgreSQL)
- Pydantic

### 前端
- React 18
- TypeScript 5
- Recharts (图表)
- Axios (HTTP客户端)
- React Router

## 许可证

MIT License - FormalMath Project
