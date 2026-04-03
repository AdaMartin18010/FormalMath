# FormalMath 认知诊断系统

基于HCD（层次约束感知认知诊断）框架的数学认知诊断系统。

## 项目结构

```
cognitive-diagnosis-system/
├── backend/                 # 后端服务 (FastAPI)
│   ├── app/
│   │   ├── api/            # API路由
│   │   ├── core/           # 核心配置
│   │   ├── models/         # 数据模型
│   │   └── services/       # 业务服务
│   │       ├── hcd_algorithm.py      # HCD诊断算法
│   │       └── question_bank.py      # 题库管理
│   ├── data/
│   │   └── question_bank.yaml        # 题库数据
│   ├── tests/              # 测试用例
│   └── requirements.txt    # Python依赖
│
├── frontend/               # 前端应用 (React + TypeScript)
│   ├── src/
│   │   ├── components/     # 组件
│   │   ├── pages/          # 页面
│   │   ├── hooks/          # 自定义Hooks
│   │   └── services/       # API服务
│   └── package.json        # Node依赖
│
├── database/               # 数据库脚本
│   └── init.sql
│
└── docs/                   # 文档
    ├── 部署说明.md
    └── API文档.md
```

## 核心功能

### 1. 诊断测试 (100+题目)
- **L0基础概念**: 30题 - 群、环、域、极限、连续性、拓扑基础等
- **L1定义理解**: 35题 - 形式化定义、基本定理、简单证明
- **L2定理应用**: 35题 - Sylow定理、Galois理论、Lebesgue积分等
- **L3综合证明**: 20题 - 概形理论、谱定理、四维流形等

### 2. HCD诊断算法
- 知识状态估计 (EM算法)
- 能力水平评估 (L0-L3)
- 层次约束应用
- 学习建议生成

### 3. 报告生成系统
- 个人诊断报告
- 知识掌握度热力图
- 学习建议生成
- 推荐学习路径

### 4. Web界面
- React 18 + TypeScript
- Ant Design UI组件
- ECharts数据可视化
- KaTeX数学公式渲染

## 快速开始

### 后端启动
```bash
cd backend
python -m venv venv
source venv/bin/activate  # Windows: venv\Scripts\activate
pip install -r requirements.txt
uvicorn app.main:app --reload
```

### 前端启动
```bash
cd frontend
npm install
npm run dev
```

## API文档

详见 [docs/API文档.md](docs/API文档.md)

### 核心接口

```http
POST   /api/v1/diagnosis/start      # 开始诊断
POST   /api/v1/diagnosis/submit     # 提交答案
GET    /api/v1/diagnosis/{id}/result # 获取结果
GET    /api/v1/students/{id}/profile # 学生档案
GET    /api/v1/students/{id}/learning-path # 学习路径
```

## 技术栈

| 层级 | 技术 |
|------|------|
| 后端 | Python, FastAPI, SQLAlchemy, PostgreSQL |
| 算法 | NumPy, SciPy |
| 前端 | React, TypeScript, Ant Design, ECharts |
| 部署 | Docker, Docker Compose |

## 文档

- [部署说明](docs/部署说明.md)
- [API文档](docs/API文档.md)
- [使用指南](../../docs/00-认知诊断系统使用指南.md)

## 许可证

MIT License
