---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# FormalMath AI学习助手

智能数学学习辅助系统的AI服务模块，集成LLM提供数学概念问答、证明辅助、学习建议等功能。

## 功能特性

### 核心功能

- **🎓 概念解释**: 支持不同难度级别的数学概念解释
  - 入门级(beginner): 通俗语言和日常类比
  - 中级(intermediate): 标准技术解释
  - 高级(advanced): 严格数学定义和深度讨论

- **💡 证明提示**: 提供证明的启发式指导
  - 证明策略建议
  - 关键引理提示
  - 不直接给出答案，引导自主思考

- **📖 学习建议**: 个性化学习路径推荐
  - 基于学习目标定制
  - 考虑用户知识水平
  - 推荐资源和练习

- **✏️ 问题解答**: 数学问题求解
  - 详细步骤展示
  - 多种解法说明
  - 验证和反思

- **🔧 Lean 4支持**: 形式化数学帮助
  - 自然语言到Lean代码转换
  - 证明策略建议
  - 形式化验证

### 技术特性

- **多LLM支持**: DeepSeek、OpenAI等
- **语义搜索集成**: 与现有知识图谱结合
- **多轮对话**: 支持上下文记忆
- **LaTeX渲染**: 数学公式自动提取和渲染
- **对话管理**: 会话创建、续接、导出

## 项目结构

```
ai-assistant/
├── backend/                 # 后端服务
│   ├── app/
│   │   ├── api/            # API路由
│   │   │   └── routes.py   # 主要API端点
│   │   ├── core/           # 核心配置
│   │   │   └── config.py
│   │   ├── llm/            # LLM客户端
│   │   │   ├── client.py   # 主客户端
│   │   │   ├── providers.py # LLM提供商
│   │   │   └── math_prompts.py # 数学提示词
│   │   ├── knowledge/      # 知识库集成
│   │   │   ├── knowledge_service.py
│   │   │   └── context_builder.py
│   │   ├── services/       # 核心服务
│   │   │   ├── ai_assistant.py
│   │   │   └── conversation_manager.py
│   │   └── __init__.py
│   ├── main.py             # 应用入口
│   └── requirements.txt
├── frontend/               # 前端组件
│   └── src/
│       ├── api/            # API客户端
│       └── components/     # React组件
├── docs/                   # 文档
│   └── API.md              # API文档
└── README.md
```

## 快速开始

### 1. 安装依赖

```bash
cd backend
pip install -r requirements.txt
```

### 2. 配置环境变量

创建 `.env` 文件:

```env
# LLM配置
LLM_PROVIDER=deepseek
LLM_MODEL=deepseek-chat
LLM_API_KEY=your_api_key_here
LLM_BASE_URL=https://api.deepseek.com

# 或OpenAI配置
# LLM_PROVIDER=openai
# LLM_API_KEY=your_openai_key
# LLM_MODEL=gpt-4

# 服务配置
DEBUG=false
PORT=8001
```

### 3. 启动服务

```bash
python main.py
```

或:

```bash
uvicorn main:app --host 0.0.0.0 --port 8001 --reload
```

### 4. 访问API文档

- Swagger UI: http://localhost:8001/docs
- ReDoc: http://localhost:8001/redoc

## API端点

| 端点 | 方法 | 描述 |
|------|------|------|
| `/api/v1/ai-assistant/ask` | POST | 通用问答 |
| `/api/v1/ai-assistant/explain` | POST | 概念解释 |
| `/api/v1/ai-assistant/proof-hint` | POST | 证明提示 |
| `/api/v1/ai-assistant/learning-advice` | POST | 学习建议 |
| `/api/v1/ai-assistant/solve` | POST | 问题解答 |
| `/api/v1/ai-assistant/lean-help` | POST | Lean 4帮助 |
| `/api/v1/ai-assistant/conversations` | POST/GET | 对话管理 |

详见 [API文档](./docs/API.md)

## 使用示例

### 概念解释

```python
import requests

response = requests.post("http://localhost:8001/api/v1/ai-assistant/explain", json={
    "concept": "群论",
    "level": "beginner"
})

print(response.json()["answer"])
```

### 证明提示

```python
response = requests.post("http://localhost:8001/api/v1/ai-assistant/proof-hint", json={
    "theorem": "证明：任何有限群都有合成列",
    "user_attempt": "我尝试用归纳法..."
})
```

### 学习建议

```python
response = requests.post("http://localhost:8001/api/v1/ai-assistant/learning-advice", json={
    "goal": "我想在3个月内掌握代数几何基础",
    "user_id": "user_123"
})
```

## 与主API集成

AI助手服务设计为可独立运行，也可与FormalMath主API集成:

```python
# 在主API中导入AI助手路由
from ai_assistant.backend.app.api.routes import router as ai_router

app.include_router(
    ai_router,
    prefix="/api/v1"
)
```

## 架构设计

```
┌─────────────────────────────────────────────────────────────┐
│                        用户请求                              │
└───────────────────────┬─────────────────────────────────────┘
                        │
┌───────────────────────▼─────────────────────────────────────┐
│                    API路由层                                 │
│  /ask /explain /proof-hint /learning-advice /solve /lean    │
└───────────────────────┬─────────────────────────────────────┘
                        │
┌───────────────────────▼─────────────────────────────────────┐
│                  AI助手核心服务                              │
│              (意图分类 + 路由分发)                           │
└───────────────────────┬─────────────────────────────────────┘
                        │
        ┌───────────────┼───────────────┐
        ▼               ▼               ▼
┌──────────────┐ ┌─────────────┐ ┌──────────────┐
│   LLM客户端   │ │  知识库服务  │ │  对话管理器   │
│  DeepSeek    │ │ 语义搜索    │ │ 上下文管理   │
│  OpenAI      │ │ 知识图谱    │ │ 会话持久化   │
└──────────────┘ └─────────────┘ └──────────────┘
```

## 配置选项

| 环境变量 | 说明 | 默认值 |
|----------|------|--------|
| `LLM_PROVIDER` | LLM提供商 | `deepseek` |
| `LLM_MODEL` | 模型名称 | `deepseek-chat` |
| `LLM_API_KEY` | API密钥 | - |
| `LLM_TEMPERATURE` | 温度参数 | `0.7` |
| `LLM_MAX_TOKENS` | 最大token数 | `4096` |
| `MAX_SESSIONS_PER_USER` | 每用户最大会话数 | `10` |
| `SESSION_TIMEOUT_MINUTES` | 会话超时时间(分钟) | `60` |
| `MAX_MESSAGES_PER_SESSION` | 每会话最大消息数 | `100` |

## 贡献指南

欢迎贡献代码！请遵循以下步骤:

1. Fork仓库
2. 创建功能分支 (`git checkout -b feature/amazing-feature`)
3. 提交更改 (`git commit -m 'Add amazing feature'`)
4. 推送分支 (`git push origin feature/amazing-feature`)
5. 创建Pull Request

## 许可证

MIT License - 详见项目根目录LICENSE文件
