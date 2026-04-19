---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 认知诊断系统 (Cognitive Diagnosis System)
---
# 认知诊断系统 (Cognitive Diagnosis System)

FormalMath 项目 T2.1 组件 - 基于 HCD（层级认知诊断）框架的智能诊断系统。

## 系统概述

本系统实现基于层次约束感知的认知诊断框架（Hierarchical Cognitive Diagnosis, HCD），支持 L0-L3 四个知识层次的诊断评估，为学习者提供个性化的学习建议。

### 核心特性

- **HCD 诊断算法**：融合 IRT 和 DINA 模型，考虑知识层次间的约束关系
- **L0-L3 知识层次**：覆盖从基础理解到研究层次的完整能力评估
- **自适应测试**：根据答题情况动态调整题目难度
- **可视化报告**：雷达图、饼图等多种方式展示诊断结果
- **个性化建议**：基于诊断结果生成针对性学习路径和方法建议

## 技术栈

### 后端
- **FastAPI** - 高性能 Python Web 框架
- **Pydantic** - 数据验证和序列化
- **NumPy** - 数值计算（用于 HCD 算法）
- **PostgreSQL** - 数据库（当前使用内存数据库演示）

### 前端
- **React 18** - UI 框架
- **TypeScript** - 类型安全
- **Chart.js** - 数据可视化
- **Axios** - HTTP 客户端

## 目录结构

```
cognitive-diagnosis/
├── backend/
│   ├── app/
│   │   ├── api/              # API 路由
│   │   │   ├── diagnosis.py  # 诊断接口
│   │   │   ├── questions.py  # 题目接口
│   │   │   └── reports.py    # 报告接口
│   │   ├── core/             # 核心配置
│   │   ├── database/         # 数据库层
│   │   ├── diagnosis/        # 诊断引擎
│   │   │   ├── hcd_engine.py       # HCD 算法实现
│   │   │   ├── test_generator.py   # 测试生成器
│   │   │   └── report_generator.py # 报告生成器
│   │   ├── models/           # 数据模型
│   │   ├── services/         # 服务层
│   │   └── main.py           # 应用入口
│   ├── requirements.txt
│   ├── Dockerfile
│   └── run.py
├── frontend/
│   ├── public/
│   ├── src/
│   │   ├── api/              # API 客户端
│   │   ├── components/
│   │   │   └── Diagnosis/    # 诊断组件
│   │   ├── pages/            # 页面组件
│   │   ├── types/            # TypeScript 类型
│   │   └── App.tsx
│   ├── package.json
│   └── tsconfig.json
└── README.md
```

## API 接口列表

### 诊断接口
| 方法 | 路径 | 描述 |
|------|------|------|
| POST | `/api/diagnosis/start` | 开始诊断 |
| POST | `/api/diagnosis/submit` | 提交答案 |
| GET | `/api/diagnosis/session/{id}` | 获取会话状态 |
| POST | `/api/diagnosis/complete/{id}` | 完成诊断 |

### 题目接口
| 方法 | 路径 | 描述 |
|------|------|------|
| GET | `/api/questions/` | 获取题目列表 |
| GET | `/api/questions/{id}` | 获取单个题目 |
| GET | `/api/questions/random` | 获取随机题目 |

### 报告接口
| 方法 | 路径 | 描述 |
|------|------|------|
| GET | `/api/reports/user/{user_id}` | 获取用户报告列表 |
| GET | `/api/reports/{id}` | 获取报告详情 |
| GET | `/api/reports/{id}/summary` | 获取报告摘要 |
| GET | `/api/reports/{id}/comparison` | 报告对比 |

## 运行说明

### 后端启动

```bash
# 进入后端目录
cd backend

# 创建虚拟环境
python -m venv venv

# 激活虚拟环境
# Windows:
venv\Scripts\activate
# macOS/Linux:
source venv/bin/activate

# 安装依赖
pip install -r requirements.txt

# 启动服务
python run.py
```

或使用 uvicorn 直接启动：
```bash
uvicorn app.main:app --reload --host 0.0.0.0 --port 8000
```

后端服务将运行在 

API 文档：

### 前端启动

```bash
# 进入前端目录
cd frontend

# 安装依赖
npm install

# 启动开发服务器
npm start
```

前端服务将运行在 

### Docker 部署

```bash
# 构建镜像
docker build -t cognitive-diagnosis-backend ./backend

# 运行容器
docker run -p 8000:8000 cognitive-diagnosis-backend
```

## HCD 算法说明

### 核心流程

1. **初始化知识状态**
   - 基于先验知识或默认概率初始化

2. **IRT 模型更新**
   - 使用 2PL-IRT 模型估计能力参数
   - P(θ) = 1 / (1 + exp(-a(θ - b)))

3. **DINA 模型精细调整**
   - 考虑猜测(guessing)和失误(slip)参数
   - 提高诊断精度

4. **应用层次约束**
   - 先修约束：L(n+1) 的掌握度不应超过 L(n)
   - 能力约束：考虑层次间的依赖关系

5. **输出诊断结果**
   - 各知识点掌握概率
   - L0-L3 能力水平评估
   - 置信度估计

### 约束策略

- **软约束**：对违反约束的情况施加惩罚
- **硬约束**：强制满足所有层次约束

## 知识层次定义

| 层次 | 名称 | 内容规模 | 评估重点 |
|------|------|----------|----------|
| L0 | 基础层 | 1000-2000字 | 直观理解、基本定义、简单例子 |
| L1 | 中级层 | 2000-4000字 | 形式化定义、基本定理、证明思路 |
| L2 | 高级层 | 4000-6000字 | 深入定理、复杂应用、前沿内容 |
| L3 | 研究层 | 6000+字 | 开放问题、研究方向、前沿研究 |

## 开发计划

- [x] HCD 算法核心实现
- [x] 知识图谱模型
- [x] 诊断引擎模块
- [x] RESTful API 接口
- [x] 前端诊断界面
- [x] 报告可视化组件
- [ ] PostgreSQL 数据库迁移
- [ ] 用户认证系统
- [ ] 自适应题目推荐
- [ ] 学习路径规划

## 许可证

MIT License - FormalMath 项目
